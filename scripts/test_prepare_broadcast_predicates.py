"""Check predicate preparation and rejected callbacks against the original corpus."""

import importlib.util
import json
from pathlib import Path
import pickle
import random
import sys
import tempfile
import types
import unittest



ROOT = Path(__file__).resolve().parents[1]
CORPUS = ROOT.parent / 'submissions-2025' / '04-broadcast'


def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


prepare = load_module('prepare_broadcast_predicates', ROOT / 'scripts/prepare_broadcast_predicates.py')


class PredicateTests(unittest.TestCase):
    def test_wrapper_refreshes_after_each_callback(self):
        namespace = {}
        source = '''
class BroadcastProcess:
    def __init__(self): self.seen = set()
    def on_start(self, ctx): pass
    def on_local_message(self, msg, ctx): self.seen.add(msg)
    def on_message(self, msg, sender, ctx): self.seen.add(msg)
    def on_timer(self, name, ctx): self.seen.add(name)
'''
        exec(prepare.adapted_source(source, 'msg not in self.seen'), namespace)
        process = namespace['BroadcastProcess']()
        installed = []
        ctx = types.SimpleNamespace(set_predicate=installed.append)
        process.on_start(ctx)
        process.on_local_message('a', ctx)
        process.on_message('b', '0', ctx)
        process.on_timer('c', ctx)
        self.assertEqual(len(installed), 4)
        self.assertFalse(installed[-1]('a'))
        self.assertTrue(installed[-1]('new'))

    def test_generation_preserves_original_and_helpers(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            directory = root / 'original'
            submission = directory / 'fixture'
            submission.mkdir(parents=True)
            source = 'class BroadcastProcess: pass\n'
            (submission / 'broadcast.py').write_text(source)
            (submission / 'helper.py').write_text('VALUE = 1\n')
            digest = prepare.hashlib.sha256(source.encode()).hexdigest()
            prepare.RULES['fixture'] = {'sha256': digest, 'predicate': 'True',
                                        'kind': 'exact-return', 'reason': 'test'}
            self.addCleanup(prepare.RULES.pop, 'fixture')
            summary = root / 'summary.json'
            summary.write_text(json.dumps({'submissions': {'fixture': {
                'passed': True, 'counts': {'pass': 5, 'timeout': 0}}}}))
            result = prepare.prepare(directory, summary, root / 'variants')
            self.assertEqual(result['counts'], {'adapted': 1})
            self.assertEqual((submission / 'broadcast.py').read_text(), source)
            self.assertEqual((root / 'variants/submissions/fixture/helper.py').read_text(),
                             'VALUE = 1\n')

    @unittest.skipUnless(CORPUS.exists(), 'optional local submission corpus absent')
    def test_afonkin_accepts_early_ack_but_rejects_completed_ack(self):
        api = load_module('anysystem', ROOT / 'crates/must-python/src/anysystem.py')
        name = 'afonkin_pavel_v'
        module = load_module('_early_ack', CORPUS / name / 'broadcast.py')
        process = module.BroadcastProcess('0', ['0', '1', '2'])
        ack = api.Message('ACK', {'sn': 0, 'sender': '0'})
        predicate = compile(prepare.RULES[name]['predicate'], '<predicate>', 'eval')
        accepts = lambda: eval(predicate, {**module.__dict__, 'self': process, 'msg': ack})
        self.assertTrue(accepts())
        ctx = api.Context(None)
        process.on_message(ack, '1', ctx)
        self.assertEqual(ctx._actions(), [])
        process.on_message(api.Message('BCAST', {'sn': 0, 'sender': '0', 'text': 'x',
                                               'vc': {'0': 0, '1': -1, '2': -1}}),
                           '0', api.Context(None))
        self.assertTrue(accepts())
        process.on_message(ack, '1', api.Context(None))
        process.on_message(ack, '2', api.Context(None))
        self.assertFalse(accepts())

    @unittest.skipUnless(CORPUS.exists(), 'optional local submission corpus absent')
    def test_rejected_callbacks_are_existing_noops(self):
        api = load_module('anysystem', ROOT / 'crates/must-python/src/anysystem.py')
        observations = {}
        for name, rule in sorted(prepare.RULES.items()):
            if name == 'fixture':
                continue
            with self.subTest(submission=name):
                path = CORPUS / name / 'broadcast.py'
                self.assertEqual(prepare.hashlib.sha256(path.read_bytes()).hexdigest(),
                                 rule['sha256'])
                module = load_module('_audit_' + name, path)
                predicate = compile(rule['predicate'], '<predicate>', 'eval')
                rejected = 0
                for seed in range(12):
                    rng = random.Random(seed)
                    processes = [module.BroadcastProcess(str(i), ['0', '1', '2'])
                                 for i in range(3)]
                    pending = []
                    permanently_rejected = [dict() for _ in range(3)]

                    def commit(sender, ctx):
                        for action in ctx._actions():
                            if action['op'] == 'send':
                                pending.append((sender, int(action['to']), action['message']))

                    for i, process in enumerate(processes):
                        ctx = api.Context(None)
                        process.on_start(ctx)
                        commit(str(i), ctx)
                    for text in ['first', 'second']:
                        ctx = api.Context(None)
                        processes[0].on_local_message(api.Message('SEND', {'text': text}), ctx)
                        commit('0', ctx)
                    for _ in range(512):
                        if not pending:
                            break
                        sender, destination, wire = pending.pop(rng.randrange(len(pending)))
                        process = processes[destination]
                        msg = api.Message.from_json(wire['kind'], wire['data'])
                        before = pickle.dumps(process.__dict__)
                        accept = eval(predicate, {**module.__dict__, 'self': process, 'msg': msg})
                        self.assertEqual(pickle.dumps(process.__dict__), before,
                                         f'{name}: predicate mutates process')
                        ctx = api.Context(None)
                        process.on_message(msg, sender, ctx)
                        if not accept:
                            rejected += 1
                            permanently_rejected[destination][(wire['kind'], wire['data'])] = wire
                            self.assertEqual(ctx._actions(), [], f'{name}: skipped output')
                            self.assertEqual(pickle.dumps(process.__dict__), before,
                                             f'{name}: skipped state mutation')
                        commit(str(destination), ctx)
                        for previous in permanently_rejected[destination].values():
                            old_msg = api.Message.from_json(previous['kind'], previous['data'])
                            self.assertFalse(eval(predicate, {**module.__dict__, 'self': process,
                                                              'msg': old_msg}),
                                             f'{name}: rejected message became relevant again')
                observations[name] = rejected
        print('Sampled rejected callbacks:', json.dumps(observations, sort_keys=True))


if __name__ == '__main__':
    unittest.main()
