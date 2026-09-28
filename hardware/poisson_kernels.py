"""Restricted, directly authored binary64 PTX for the Poisson numerical backend.

This is not an exporter from the verified FP32 instruction model. The explicit
stages correspond to Poisson.localAction and solvePCG and are checked empirically.
"""
import math
import struct

ZERO='0d0000000000000000'
ONE='0d3ff0000000000000'
MAX='0d7fefffffffffffff'


class Layout:
    def __init__(self, reference, options):
        n,p=reference['n'],reference['degree']
        if type(n) is not int or n<1 or type(p) is not int or p not in (1,2,3,4):
            raise ValueError('expected positive n and degree 1..4')
        self.n,self.p,self.m=n,p,p+1
        self.size=(n*p+1)**2
        if self.size>=2**30 or n*n*(p+1)**2>=2**30:
            raise ValueError('index domain exceeds 32-bit bound')
        self.fields={};self.data=bytearray();self.launches={}
        def add(name,values,kind='d',mutable=False):
            self.data.extend(b'\xa5'*((-len(self.data))%8))
            self.fields[name]=dict(offset=len(self.data),count=len(values),kind=kind,mutable=mutable)
            self.data.extend(struct.pack('<'+kind*len(values),*values))
            # Guard each logical buffer, not just the outer allocation.
            self.data.extend(b'\xa5'*32)
        for key in ('B','D'):
            values=reference[key]
            if len(values)!=self.m**2 or not all(math.isfinite(x) for x in values):
                raise ValueError('invalid basis table')
            add(key,values)
        weights=reference['weights']
        if len(weights)!=self.m or not all(math.isfinite(w) and w>0 for w in weights):
            raise ValueError('invalid quadrature weights')
        add('W',[a*b for a in weights for b in weights])
        cells=reference['cells'];width=n*p+1
        expected=[[(ey*p+i)*width+ex*p+j for i in range(p+1) for j in range(p+1)]
                  for ey in range(n) for ex in range(n)]
        if cells!=expected:raise ValueError('connectivity is not the supported uniform mesh')
        add('cells',[j for row in cells for j in row],'I')
        bd=[int(i%width in (0,width-1) or i//width in (0,width-1)) for i in range(self.size)]
        if bd!=reference['boundary']:raise ValueError('boundary mask mismatch')
        add('boundary',bd,'I')
        incident=[[] for _ in range(self.size)]
        for e,cell in enumerate(cells):
            for i,node in enumerate(cell):incident[node].append(e*self.m**2+i)
        offsets=[0];entries=[]
        for xs in incident:
            entries.extend(xs);offsets.append(len(entries))
        add('offsets',offsets,'I');add('entries',entries,'I')
        for key in ('load','diagonal','probe'):
            values=reference[key]
            if len(values)!=self.size or not all(math.isfinite(x) for x in values):
                raise ValueError(f'invalid {key}')
            if key=='diagonal' and any(v<=0 for v,b in zip(values,bd) if not b):
                raise ValueError('Jacobi diagonal must be positive')
            add(key,values)
        rtol,atol=options.get('rtol',1e-10),options.get('atol',0.)
        if not all(type(v) in (int,float) and math.isfinite(v) and v>=0 for v in (rtol,atol)) or not(rtol or atol):
            raise ValueError('invalid tolerances')
        for k,minimum in (('maxiter',0),('check_every',1)):
            v=options.get(k,1000 if k=='maxiter' else 10)
            if type(v) is not int or v<minimum:raise ValueError(f'invalid {k}')
        add('rtol',[rtol]);add('atol',[atol])
        for key in ('x','rhs','r','z','p','ap','true_r','applied'):
            add(key,[0.]*self.size,mutable=True)
        add('element',[0.]*(n*n*self.m*self.m),mutable=True)
        for key in ('rho','rho_next','denominator','rr','rhs_square','true_square','rhs_norm','residual','tolerance','alpha','beta'):
            add(key,[0.],mutable=True)
        for key in ('active','broken','use_step'):add(key,[0],'I',mutable=True)

    def offset(self,name):return self.fields[name]['offset']
    def manifest(self):return dict(n=self.n,degree=self.p,bytes=len(self.data),fields=self.fields,launches=self.launches)


class PTX:
    def __init__(self,layout):self.l=layout
    def address(self,field,index='0'):
        size=8 if self.l.fields[field]['kind']=='d' else 4
        return f'mul.wide.u32 %off, {index}, {size};\nadd.u64 %addr, %base, %off;\nadd.u64 %addr, %addr, {self.l.offset(field)};\n'
    def load(self,field,reg,index='0'):
        typ='f64' if self.l.fields[field]['kind']=='d' else 'u32'
        return self.address(field,index)+f'ld.global.{typ} {reg}, [%addr];\n'
    def store(self,field,reg,index='0'):
        typ='f64' if self.l.fields[field]['kind']=='d' else 'u32'
        return self.address(field,index)+f'st.global.{typ} [%addr], {reg};\n'
    def entry(self,name,body,threads=256,groups=None,shared=0):
        if groups is None:groups=(self.l.size+threads-1)//threads
        self.l.launches[name]=dict(groups=groups,threads=threads,shared_bytes=shared)
        return f'''.visible .entry {name}(.param .u64 arena)
.reqntid {threads}, 1, 1
{{
.reg .u32 %lane, %cell, %i, %j, %k, %idx, %node, %cursor, %end, %other, %flag, %flag2, %global;
.reg .b64 %base, %off, %addr, %shared;
.reg .f64 %a, %b, %c, %d, %acc, %acc2, %prod, %value;
.reg .pred %live, %p0, %p1, %p2, %p3;
'''+(f'.shared .align 8 .b8 scratch[{shared}];\nmov.u64 %shared, scratch;\n' if shared else '')+f'''ld.param.u64 %base, [arena];
mov.u32 %lane, %tid.x;
mov.u32 %cell, %ctaid.x;
'''+body+'ret;\n}\n'
    def vector_start(self):
        return f'mad.lo.u32 %global, %cell, 256, %lane;\nsetp.ge.u32 %p0, %global, {self.l.size};\n@%p0 ret;\n'
    def index(self,row,col):
        return f'mul.lo.u32 %idx, {row}, {self.l.m};\nadd.u32 %idx, %idx, {col};\n'
    def shared_load(self,plane,row,col,reg):
        return self.index(row,col)+f'mul.wide.u32 %off, %idx, 8;\nadd.u64 %addr, %shared, %off;\nld.shared.f64 {reg}, [%addr+{plane*self.l.m**2*8}];\n'
    def shared_store(self,plane,reg):
        return f'mul.wide.u32 %off, %lane, 8;\nadd.u64 %addr, %shared, %off;\nst.shared.f64 [%addr+{plane*self.l.m**2*8}], {reg};\n'
    def operand(self,plane,row,col,reg):
        if isinstance(plane,int):return self.shared_load(plane,row,col,reg)
        return self.index(row,col)+self.load(plane,reg,'%idx')
    def dot(self,a,b,acc='%acc'):
        code=f'mov.f64 {acc}, {ZERO};\n'
        for k in range(self.l.m):
            aa=[str(k) if x=='k' else x for x in a[1:]]
            bb=[str(k) if x=='k' else x for x in b[1:]]
            code+=self.operand(a[0],*aa,'%a')+self.operand(b[0],*bb,'%b')
            code+=f'mul.rn.f64 %prod, %a, %b;\nadd.rn.f64 {acc}, {acc}, %prod;\n'
        return code
    def element(self,name,source):
        m=self.l.m
        body=f'setp.lt.u32 %live, %lane, {m*m};\ndiv.u32 %i, %lane, {m};\nrem.u32 %j, %lane, {m};\n'
        stages=[]
        stages.append(f'mad.lo.u32 %idx, %cell, {m*m}, %lane;\n'+self.load('cells','%node','%idx')+self.load(source,'%value','%node')+self.shared_store(0,'%value'))
        stages.append(self.dot(('B','%i','k'),(0,'k','%j'))+self.shared_store(1,'%acc')+
                      self.dot(('D','%i','k'),(0,'k','%j'))+self.shared_store(2,'%acc'))
        stages.append(self.dot((1,'%i','k'),('D','%j','k'))+self.load('W','%c','%lane')+
                      'mul.rn.f64 %acc, %acc, %c;\n'+self.shared_store(3,'%acc')+
                      self.dot((2,'%i','k'),('B','%j','k'))+self.load('W','%c','%lane')+
                      'mul.rn.f64 %acc, %acc, %c;\n'+self.shared_store(4,'%acc'))
        stages.append(self.dot(('B','k','%i'),(3,'k','%j'))+self.shared_store(5,'%acc')+
                      self.dot(('D','k','%i'),(4,'k','%j'))+self.shared_store(6,'%acc'))
        stages.append(self.dot((5,'%i','k'),('D','k','%j'))+self.dot((6,'%i','k'),('B','k','%j'),'%acc2')+
                      f'add.rn.f64 %value, %acc, %acc2;\nmad.lo.u32 %idx, %cell, {m*m}, %lane;\n'+self.store('element','%value','%idx'))
        for i,stage in enumerate(stages):
            body+=f'@!%live bra stage_{i}_done;\n'+stage+f'stage_{i}_done:\n'
            if i<len(stages)-1:body+='bar.sync 0;\n'
        return self.entry(name,body,32,self.l.n**2,7*m*m*8)
    def assemble(self,name,target,mask):
        body=self.vector_start()+self.load('offsets','%cursor','%global')+'add.u32 %idx, %global, 1;\n'+self.load('offsets','%end','%idx')
        body+=f'mov.f64 %acc, {ZERO};\nloop:\nsetp.ge.u32 %p0, %cursor, %end;\n@%p0 bra done;\n'
        body+=self.load('entries','%idx','%cursor')+self.load('element','%a','%idx')+'add.rn.f64 %acc, %acc, %a;\nadd.u32 %cursor, %cursor, 1;\nbra loop;\ndone:\n'
        if mask:body+=self.load('boundary','%flag','%global')+f'setp.ne.u32 %p0, %flag, 0;\n@%p0 mov.f64 %acc, {ZERO};\n'
        return self.entry(name,body+self.store(target,'%acc','%global'))
    def reduce(self,name,a,b,target):
        body=f'mov.u32 %global, %lane;\nmov.f64 %acc, {ZERO};\nloop:\nsetp.ge.u32 %p0, %global, {self.l.size};\n@%p0 bra finish;\n'
        body+=self.load(a,'%a','%global')+self.load(b,'%b','%global')+'mul.rn.f64 %prod, %a, %b;\nadd.rn.f64 %acc, %acc, %prod;\nadd.u32 %global, %global, 256;\nbra loop;\nfinish:\n'
        body+='mul.wide.u32 %off, %lane, 8;\nadd.u64 %addr, %shared, %off;\nst.shared.f64 [%addr], %acc;\nbar.sync 0;\n'
        for stride in (128,64,32,16,8,4,2,1):
            body+=f'setp.ge.u32 %p0, %lane, {stride};\n@%p0 bra next_{stride};\n'
            body+=f'mul.wide.u32 %off, %lane, 8;\nadd.u64 %addr, %shared, %off;\nld.shared.f64 %a, [%addr];\nld.shared.f64 %b, [%addr+{stride*8}];\nadd.rn.f64 %acc, %a, %b;\nst.shared.f64 [%addr], %acc;\nnext_{stride}:\nbar.sync 0;\n'
        body+='setp.ne.u32 %p0, %lane, 0;\n@%p0 ret;\nld.shared.f64 %acc, [%shared];\n'+self.store(target,'%acc')
        return self.entry(name,body,256,1,2048)
    def finite(self,reg,pred):
        return f'abs.f64 %value, {reg};\nsetp.le.f64 {pred}, %value, {MAX};\n'
    def scalar(self,name,body):return self.entry(name,body,1,1)


def module(layout,version='9.4',target='sm_120'):
    if version not in ('9.2','9.4') or target!='sm_120':raise ValueError('unreviewed PTX version or target')
    g=PTX(layout);load,store=g.load,g.store
    kernels=[g.element('element_probe','probe'),g.element('element_p','p'),g.element('element_x','x'),
             g.assemble('assemble_probe','applied',False),g.assemble('assemble_ap','ap',True)]
    for name,a,b,out in [('dot_rhs','rhs','rhs','rhs_square'),('dot_rz','r','z','rho'),
                         ('dot_pap','p','ap','denominator'),('dot_next','r','z','rho_next'),
                         ('dot_rr','r','r','rr'),('dot_true','true_r','true_r','true_square')]:
        kernels.append(g.reduce(name,a,b,out))
    body=g.vector_start()+load('boundary','%flag','%global')+load('load','%a','%global')
    body+=f'setp.ne.u32 %p0, %flag, 0;\n@%p0 mov.f64 %a, {ZERO};\n'
    body+=store('rhs','%a','%global')+store('r','%a','%global')+load('diagonal','%b','%global')
    body+=f'@%p0 mov.f64 %b, {ONE};\ndiv.rn.f64 %c, %a, %b;\n'
    body+=store('z','%c','%global')+store('p','%c','%global')+store('x',ZERO,'%global')
    kernels.append(g.entry('initialize',body))
    body=load('rhs_square','%a')+'sqrt.rn.f64 %a, %a;\n'+store('rhs_norm','%a')+store('residual','%a')
    body+=load('rtol','%b')+load('atol','%c')+'mul.rn.f64 %b, %b, %a;\nmax.f64 %b, %b, %c;\n'+store('tolerance','%b')
    body+=store('active','1')+store('broken','0')
    kernels.append(g.scalar('start',body))
    body=load('denominator','%a')+load('rho','%b')+load('active','%flag')+load('broken','%flag2')
    body+=g.finite('%a','%p0')+g.finite('%b','%p1')+f'setp.gt.f64 %p2, %a, {ZERO};\nsetp.gt.f64 %p3, %b, {ZERO};\nand.pred %p0, %p0, %p1;\nand.pred %p0, %p0, %p2;\nand.pred %p0, %p0, %p3;\nsetp.ne.u32 %p1, %flag, 0;\nnot.pred %p2, %p0;\nand.pred %p2, %p2, %p1;\n@%p2 mov.u32 %flag2, 1;\nand.pred %p0, %p0, %p1;\nselp.u32 %flag, 1, 0, %p0;\n'
    body+=store('broken','%flag2')+store('use_step','%flag')+f'mov.f64 %c, {ZERO};\n@%p0 div.rn.f64 %c, %b, %a;\n'+store('alpha','%c')
    kernels.append(g.scalar('coefficient_alpha',body))
    body=g.vector_start()+load('alpha','%a')+load('p','%b','%global')+load('x','%c','%global')
    body+='mul.rn.f64 %prod, %a, %b;\nadd.rn.f64 %c, %c, %prod;\n'+store('x','%c','%global')
    body+=load('ap','%b','%global')+load('r','%c','%global')+'mul.rn.f64 %prod, %a, %b;\nsub.rn.f64 %c, %c, %prod;\n'+store('r','%c','%global')
    body+=load('diagonal','%b','%global')+load('boundary','%flag','%global')+f'setp.ne.u32 %p0, %flag, 0;\n@%p0 mov.f64 %b, {ONE};\ndiv.rn.f64 %c, %c, %b;\n'+store('z','%c','%global')
    kernels.append(g.entry('update_xrz',body))
    body=load('rho_next','%a')+load('rho','%b')+load('active','%flag')+load('broken','%flag2')
    body+=g.finite('%a','%p0')+'not.pred %p0, %p0;\nsetp.ne.u32 %p1, %flag, 0;\nand.pred %p0, %p0, %p1;\n@%p0 mov.u32 %flag2, 1;\n'+store('broken','%flag2')
    body+=load('use_step','%flag')+f'setp.ne.u32 %p0, %flag, 0;\nmov.f64 %c, {ZERO};\n@%p0 div.rn.f64 %c, %a, %b;\n'+store('beta','%c')+store('rho','%a')
    body+=load('rr','%a')+load('tolerance','%b')+'mul.rn.f64 %b, %b, %b;\nsetp.gt.f64 %p1, %a, %b;\nsetp.eq.u32 %p2, %flag2, 0;\nand.pred %p0, %p0, %p1;\nand.pred %p0, %p0, %p2;\nselp.u32 %flag, 1, 0, %p0;\n'+store('active','%flag')
    kernels.append(g.scalar('coefficient_beta',body))
    body=g.vector_start()+load('beta','%a')+load('p','%b','%global')+load('z','%c','%global')+'mul.rn.f64 %prod, %a, %b;\nadd.rn.f64 %c, %c, %prod;\n'+store('p','%c','%global')
    kernels.append(g.entry('update_p',body))
    body=g.vector_start()+load('rhs','%a','%global')+load('ap','%b','%global')+'sub.rn.f64 %c, %a, %b;\n'+store('true_r','%c','%global')
    kernels.append(g.entry('true_residual',body))
    kernels.append(g.scalar('residual_norm',load('true_square','%a')+'sqrt.rn.f64 %a, %a;\n'+store('residual','%a')))
    body=g.vector_start()+load('true_r','%a','%global')+store('r','%a','%global')+load('diagonal','%b','%global')+load('boundary','%flag','%global')+f'setp.ne.u32 %p0, %flag, 0;\n@%p0 mov.f64 %b, {ONE};\ndiv.rn.f64 %c, %a, %b;\n'+store('z','%c','%global')+store('p','%c','%global')
    kernels.append(g.entry('restart_vectors',body))
    kernels.append(g.scalar('restart_flag',store('active','1')))
    return f'.version {version}\n.target {target}\n.address_size 64\n\n'+'\n'.join(kernels)
