"""Persistent guarded CUDA storage and host control for the PTX PCG stages."""
import ctypes as C
import math
import struct
import uuid

from cuda_driver import Cuda


class Session:
    def __init__(self, layout, cubin):
        self.layout=layout;self.cuda=Cuda();self.module=C.c_void_p();self.pointer=C.c_uint64()
        self.loaded=self.allocated=False;self.functions={};self.launch_log=[]
        self.initial=b'\xa5'*64+bytes(layout.data)+b'\xa5'*64
        try:
            self.cuda.lib.cuDeviceGetName.argtypes=[C.c_void_p,C.c_int,C.c_int]
            self.cuda.lib.cuDeviceGetUuid_v2.argtypes=[C.c_void_p,C.c_int]
            name=C.create_string_buffer(256);ident=(C.c_ubyte*16)();version=C.c_int()
            self.cuda.call('cuDeviceGetName',name,256,self.cuda.device)
            self.cuda.call('cuDeviceGetUuid_v2',C.byref(ident),self.cuda.device)
            self.cuda.call('cuDriverGetVersion',C.byref(version))
            major,minor=self.cuda.attribute(75),self.cuda.attribute(76)
            if (major,minor)!=(12,0):raise ValueError('only reviewed sm_120 hardware is supported')
            self.device_info=dict(name=name.value.decode(),uuid='GPU-'+str(uuid.UUID(bytes=bytes(ident))),
                                  compute_capability=[major,minor],driver_api_version=version.value)
            self.cuda.call('cuModuleLoad',C.byref(self.module),str(cubin).encode());self.loaded=True
            self.cuda.call('cuMemAlloc_v2',C.byref(self.pointer),len(self.initial));self.allocated=True
            host=C.create_string_buffer(self.initial,len(self.initial))
            self.cuda.call('cuMemcpyHtoD_v2',self.pointer,host,len(self.initial))
            self.base=C.c_uint64(self.pointer.value+64)
            self.params=(C.c_void_p*1)(C.cast(C.byref(self.base),C.c_void_p))
        except BaseException:
            self.close();raise

    def launch(self,name):
        dims=self.layout.launches[name]
        if dims['threads']>self.cuda.attribute(1) or dims['groups']>self.cuda.attribute(5) or dims['shared_bytes']>self.cuda.attribute(8):
            raise ValueError('launch exceeds hardware resource limits')
        if name not in self.functions:
            fn=C.c_void_p();self.cuda.call('cuModuleGetFunction',C.byref(fn),self.module,name.encode());self.functions[name]=fn
        self.cuda.call('cuLaunchKernel',self.functions[name],dims['groups'],1,1,dims['threads'],1,1,0,None,self.params,None)
        self.launch_log.append(name)

    def read(self,name):
        f=self.layout.fields[name];size=struct.calcsize(f['kind'])*f['count'];host=C.create_string_buffer(size)
        self.cuda.call('cuMemcpyDtoH_v2',host,C.c_uint64(self.base.value+f['offset']),size)
        return list(struct.unpack('<'+f['kind']*f['count'],host.raw))

    def scalar(self,name):return self.read(name)[0]

    def audit_storage(self):
        self.cuda.call('cuCtxSynchronize')
        host=C.create_string_buffer(len(self.initial))
        self.cuda.call('cuMemcpyDtoH_v2',host,self.pointer,len(self.initial))
        actual=host.raw
        mutable=bytearray(len(actual))
        for f in self.layout.fields.values():
            if f['mutable']:
                start=64+f['offset'];end=start+struct.calcsize(f['kind'])*f['count']
                mutable[start:end]=b'\x01'*(end-start)
        for i,(before,after,allowed) in enumerate(zip(self.initial,actual,mutable,strict=True)):
            if not allowed and before!=after:raise AssertionError(f'input or buffer guard modified at byte {i}')
        return 'pass'

    def close(self):
        try:
            if self.allocated:self.cuda.call('cuMemFree_v2',self.pointer);self.allocated=False
        finally:
            try:
                if self.loaded:self.cuda.call('cuModuleUnload',self.module);self.loaded=False
            finally:self.cuda.close()

    def __enter__(self):return self
    def __exit__(self,*args):self.close()


def solve(session,options):
    """Only scheduling and status decisions are on CPU; all solver arithmetic is PTX."""
    s=session;trace=[];restarts=0
    s.launch('element_probe');s.launch('assemble_probe')
    applied=s.read('applied')
    s.launch('initialize');s.launch('dot_rhs');s.launch('dot_rz');s.launch('start')
    rhs_norm=s.scalar('rhs_norm');tolerance=s.scalar('tolerance')
    residual=rhs_norm
    def finish(it,reason):
        return dict(solution=s.read('x'),applied=applied,iterations=it,reason=reason,converged=reason=='converged',
                    true_residual_norm=residual,relative_residual=residual/rhs_norm if rhs_norm else 0.,
                    tolerance=tolerance,restarts=restarts,checks=trace,storage_audit=s.audit_storage(),
                    launches=s.launch_log)
    if not math.isfinite(rhs_norm):return finish(0,'breakdown')
    if rhs_norm<=tolerance:return finish(0,'converged')
    maximum=options.get('maxiter',1000);interval=options.get('check_every',10)
    if maximum==0:return finish(0,'maxiter')
    for it in range(1,maximum+1):
        for name in ('element_p','assemble_ap','dot_pap','coefficient_alpha','update_xrz','dot_next','dot_rr','coefficient_beta','update_p'):
            s.launch(name)
        if it%interval==0 or it==maximum:
            for name in ('element_x','assemble_ap','true_residual','dot_true','residual_norm'):s.launch(name)
            residual=s.scalar('residual');active=s.scalar('active');broken=s.scalar('broken')
            trace.append(dict(iteration=it,residual=residual,active=bool(active),broken=bool(broken)))
            if not math.isfinite(residual):return finish(it,'breakdown')
            if residual<=tolerance:return finish(it,'converged')
            if broken:return finish(it,'breakdown')
            if not active:
                for name in ('restart_vectors','dot_rz','restart_flag'):s.launch(name)
                restarts+=1
    return finish(maximum,'maxiter')
