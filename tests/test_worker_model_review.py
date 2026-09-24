"""Review provenance and failure behavior, with synthetic transport and source."""
import copy
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]/'scripts'))
import model_review as m


class ReviewTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(); self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.git('init','-q'); self.git('config','user.name','Test')
        self.git('config','user.email','test@example.invalid')
        self.manual = b'<section id="source"><h2>Instruction</h2><p>Preserve the input value.</p></section>'
        self.put('.gitignore',b'.ptx-source/\n.formalization-runs/\n')
        self.put('.ptx-source/9.4/index.html',self.manual)
        self.put(str(m.MANIFEST),m.encoded({'isa_version':'9.4','artifact':'index.html',
            'bytes':len(self.manual),'sha256':m.sha(self.manual),'url':'https://example.invalid'}))
        self.put('Candidate.lean',b'def compute (x : Nat) := x\n')
        self.put('Support.lean',b'def support := 1\n')
        self.git('add','.');self.git('commit','-qm','base')
        self.recipe = {'base_commit':self.git('rev-parse','HEAD').decode().strip(),
            'scope':'A synthetic identity instruction.',
            'sections':[{'anchor':'source','sha256':m.sha(self.manual)}],
            'files':[{'path':p,'role':r,'sha256':m.sha((self.root/p).read_bytes())}
                     for p,r in [('Candidate.lean','candidate'),('Support.lean','support')]],
            'obligations':[{'id':'meaning','text':'Preserve the input value.'}],
            'expected':'THIS PRIVATE LABEL MUST NOT BE SENT'}
        self.recipe_path=self.root/'recipe.json'; self.save()
        self.output=self.root/'.formalization-runs/reviews/one'
        self.report={'verdict':'accept','summary':'Identity is preserved.',
            'obligations':[{'id':'meaning','status':'satisfied','reason':'The result is x.'}],
            'findings':[],'uncertainties':[]}
        self.env=patch.dict(os.environ,{'OPENROUTER_API_KEY':'synthetic-test-secret'})
        self.env.start();self.addCleanup(self.env.stop)

    def git(self,*args):
        return subprocess.check_output(['git',*args],cwd=self.root,stderr=subprocess.PIPE)

    def put(self,name,body):
        p=self.root/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(body)

    def save(self):self.recipe_path.write_bytes(m.encoded(self.recipe))

    def response(self,**changes):
        value={'model':m.MODELS[0],'provider':'synthetic','id':'test',
            'choices':[{'finish_reason':'stop','message':{'content':json.dumps(self.report)}}],
            'usage':{'prompt_tokens':10,'completion_tokens':20}}
        value.update(changes);return io.BytesIO(m.encoded(value))

    def run_fake(self,transport=None):
        return m.run(self.recipe_path,self.output,m.MODELS[0],self.root,
                     transport=transport or (lambda *a,**k:self.response()))

    def test_packet_excludes_labels_and_mutable_checkout(self):
        self.put('Candidate.lean',b'uncommitted unrelated edit')
        packet=m.packet(self.recipe,self.root)
        self.assertNotIn('PRIVATE LABEL',json.dumps(packet))
        self.assertIn(':= x',packet['files'][0]['text'])
        self.assertEqual(m.request_body(packet,m.MODELS[0])['messages'],
                         m.request_body(packet,m.MODELS[1])['messages'])

    def test_source_and_candidate_drift_block_packet(self):
        for field in ['source','candidate']:
            recipe=copy.deepcopy(self.recipe)
            if field=='source':recipe['sections'][0]['sha256']='0'*64
            else:recipe['files'][0]['sha256']='0'*64
            with self.subTest(field=field),self.assertRaisesRegex(ValueError,'hash mismatch'):
                m.packet(recipe,self.root)

    def test_patch_is_applied_only_to_index_and_hash_checked(self):
        self.put('Candidate.lean',b'def compute (x : Nat) := x + 1\n')
        patch_bytes=self.git('diff');self.put('change.patch',patch_bytes)
        self.recipe['patch']={'path':'change.patch','sha256':m.sha(patch_bytes)}
        self.recipe['files'][0]['sha256']=m.sha((self.root/'Candidate.lean').read_bytes())
        self.git('checkout','--','Candidate.lean')
        packet=m.packet(self.recipe,self.root)
        self.assertIn('x + 1',packet['files'][0]['text'])
        self.assertNotIn(b'x + 1',(self.root/'Candidate.lean').read_bytes())
        self.put('change.patch',patch_bytes+b'changed')
        with self.assertRaisesRegex(ValueError,'patch hash'):m.packet(self.recipe,self.root)

    def test_patch_cannot_change_supporting_interface(self):
        self.put('Support.lean',b'def support := 2\n')
        body=self.git('diff');self.put('change.patch',body)
        self.recipe['patch']={'path':'change.patch','sha256':m.sha(body)}
        with self.assertRaisesRegex(ValueError,'supporting files'):m.packet(self.recipe,self.root)

    def test_success_is_recorded_but_not_semantic_acceptance(self):
        def transport(request,timeout):
            receipt=json.loads((self.output/'receipt.json').read_text())
            self.assertEqual(receipt['state'],'started')
            self.assertEqual(request.full_url,m.ENDPOINT)
            return self.response()
        record=self.run_fake(transport)
        self.assertEqual(record['state'],'completed')
        self.assertEqual(record['semantic_acceptance'],'not_performed')
        self.assertIsNone(record['reported_cost'])
        self.assertNotIn('synthetic-test-secret',''.join(p.read_text() for p in self.output.iterdir()))
        with self.assertRaises(FileExistsError):self.run_fake()

    def test_wrong_model_and_truncation_never_become_verdicts(self):
        for label,changes in [('model',{'model':'different/model'}),
            ('length',{'choices':[{'finish_reason':'length','message':{'content':json.dumps(self.report)}}]})]:
            self.output=self.output.parent/label
            with self.assertRaises(ValueError):self.run_fake(lambda *a,**k:self.response(**changes))
            receipt=json.loads((self.output/'receipt.json').read_text())
            self.assertEqual(receipt['state'],'failed');self.assertNotIn('verdict',receipt)
            self.assertTrue((self.output/'response.json').exists())

    def test_transport_failure_not_retried_or_secret_logged(self):
        calls=[]
        def fail(*args,**kwargs):
            calls.append(1);raise OSError('synthetic-test-secret')
        with self.assertRaises(OSError):self.run_fake(fail)
        self.assertEqual(len(calls),1)
        self.assertNotIn('synthetic-test-secret',(self.output/'receipt.json').read_text())

    def test_raw_outputs_cannot_be_written_to_public_directory(self):
        self.output=self.root/'formalization/results/raw'
        with self.assertRaisesRegex(ValueError,'Raw reviews'):self.run_fake()
        self.assertFalse(self.output.exists())

    def test_inconsistent_or_unbound_findings_rejected(self):
        context=m.packet(self.recipe,self.root)
        bad=copy.deepcopy(self.report);bad['obligations']=[]
        with self.assertRaises(ValueError):m.validate_report(bad,context)
        bad=copy.deepcopy(self.report);bad['verdict']='reject'
        with self.assertRaises(ValueError):m.validate_report(bad,context)
        finding={'obligation':'meaning','path':'Candidate.lean','line':1,'anchor':'source',
                 'explanation':'Mismatch','counterexample':'x=0'}
        for key,value in [('path','Support.lean'),('anchor','invented'),('line',500),('obligation','invented')]:
            bad=copy.deepcopy(self.report);bad['verdict']='reject';bad['obligations'][0]['status']='violated'
            bad['findings']=[dict(finding,**{key:value})]
            with self.subTest(key=key),self.assertRaises(ValueError):m.validate_report(bad,context)

    def test_missing_credential_makes_no_request(self):
        with patch.dict(os.environ,{},clear=True),self.assertRaisesRegex(ValueError,'API_KEY'):
            self.run_fake(lambda *a,**k:self.fail('called without credential'))
        self.assertFalse(self.output.exists())

    def test_env_file_is_data_not_executable_and_duplicate_keys_rejected(self):
        path=self.root/'.env'
        path.write_text('UNRELATED=ignored\nexport OPENROUTER_API_KEY="literal-$value" # comment\n')
        self.assertEqual(m.load_key(path),'literal-$value')
        path.write_text('OPENROUTER_API_KEY=a\nOPENROUTER_API_KEY=b\n')
        with self.assertRaises(ValueError):m.load_key(path)

    def test_report_schema_enumerates_exact_reference_ids(self):
        context=m.packet(self.recipe,self.root)
        fields=m.schema(context)['properties']['findings']['items']['properties']
        self.assertEqual(fields['anchor']['enum'],['source'])
        self.assertEqual(fields['path']['enum'],['Candidate.lean'])
        self.assertEqual(fields['obligation']['enum'],['meaning'])

    def test_total_deadline_interrupts_trickling_response_without_verdict(self):
        import signal
        import time
        calls = []
        class Trickle:
            def __enter__(self): return self
            def __exit__(self, *args): self.closed = True
            def read(self):
                while True: time.sleep(0.005)
        response = Trickle()
        previous = signal.getsignal(signal.SIGALRM)
        def transport(*args, **kwargs):
            calls.append(1)
            return response
        started = time.monotonic()
        with self.assertRaises(m.ReviewDeadlineExceeded):
            m.run(self.recipe_path, self.output, m.MODELS[0], self.root,
                  transport=transport, total_timeout=0.05)
        self.assertLess(time.monotonic() - started, 3)
        receipt = json.loads((self.output/'receipt.json').read_text())
        self.assertEqual(receipt['failure_stage'], 'deadline')
        self.assertEqual(receipt['state'], 'failed')
        self.assertEqual(receipt['total_timeout_seconds'], 0.05)
        self.assertIsNone(receipt['reported_cost'])
        self.assertNotIn('verdict', receipt)
        self.assertFalse((self.output/'response.json').exists())
        self.assertTrue(response.closed)
        self.assertEqual(calls, [1])
        self.assertEqual(signal.getsignal(signal.SIGALRM), previous)
        self.assertEqual(signal.getitimer(signal.ITIMER_REAL), (0, 0))

    def test_total_deadline_also_covers_connection_and_releases_alarm(self):
        import signal
        import time
        def blocked(*args, **kwargs): time.sleep(3)
        with self.assertRaises(m.ReviewDeadlineExceeded):
            m.run(self.recipe_path, self.output, m.MODELS[0], self.root,
                  transport=blocked, total_timeout=0.05)
        self.assertEqual(signal.getitimer(signal.ITIMER_REAL), (0, 0))
        self.output = self.output.parent/'after-deadline'
        self.assertEqual(self.run_fake()['state'], 'completed')

    def test_invalid_deadline_rejected_before_reservation_or_request(self):
        for invalid in [0, -1, float('inf'), float('nan'), True]:
            with self.subTest(invalid=invalid), self.assertRaises(ValueError):
                m.run(self.recipe_path, self.output, m.MODELS[0], self.root,
                      transport=lambda *a, **k: self.fail('request sent'), total_timeout=invalid)
            self.assertFalse(self.output.exists())

    def test_existing_alarm_is_not_overwritten(self):
        import signal
        signal.setitimer(signal.ITIMER_REAL, 30)
        try:
            with self.assertRaisesRegex(ValueError, 'existing process alarm'):
                self.run_fake()
            self.assertGreater(signal.getitimer(signal.ITIMER_REAL)[0], 20)
            self.assertFalse(self.output.exists())
        finally:
            signal.setitimer(signal.ITIMER_REAL, 0)
