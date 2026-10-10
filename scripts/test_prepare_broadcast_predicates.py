"""Check predicate preparation and rejected callbacks against the original corpus."""

import importlib.util
import copy
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

    def test_sender_api_is_explicit_and_preserves_message_only_predicates(self):
        api = load_module('anysystem', ROOT / 'crates/must-python/src/anysystem.py')
        ctx = api.Context(None)
        msg = api.Message('X', {'sender': 'spoofed'})
        ctx.set_sender_predicate(lambda message, sender: sender == '1')
        self.assertTrue(api._matches_predicate(ctx._predicate, msg, '1'))
        self.assertFalse(api._matches_predicate(ctx._predicate, msg, '2'))
        with self.assertRaises(TypeError):
            api._matches_predicate(ctx._predicate, msg)
        ctx.set_predicate(lambda message: message.type == 'X')
        self.assertTrue(api._matches_predicate(ctx._predicate, msg, '2'))
        ctx.set_sender_predicate(None)
        self.assertTrue(api._matches_predicate(ctx._predicate, msg))
        with self.assertRaises(TypeError):
            ctx.set_sender_predicate(3)

    def test_sender_wrapper_installs_explicit_filter(self):
        namespace = {}
        source = "class BroadcastProcess:\n    def on_start(self, ctx): pass\n"
        exec(prepare.adapted_source(source, "sender == '1'", True), namespace)
        installed = []
        namespace['BroadcastProcess']().on_start(
            types.SimpleNamespace(set_sender_predicate=installed.append))
        self.assertTrue(installed[0](None, '1'))
        self.assertFalse(installed[0](None, '2'))

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

    def test_state_cache_requires_exact_audit_and_include_failing_is_explicit(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            directory = root / 'original'
            submission = directory / 'statefixture'
            submission.mkdir(parents=True)
            source = 'class BroadcastProcess: pass\n'
            (submission / 'broadcast.py').write_text(source)
            digest = prepare.hashlib.sha256(source.encode()).hexdigest()
            prepare.STATE_CACHE_AUDITS['statefixture'] = digest
            self.addCleanup(prepare.STATE_CACHE_AUDITS.pop, 'statefixture')
            summary = root / 'summary.json'
            summary.write_text(json.dumps({'submissions': {'statefixture': {
                'passed': False, 'counts': {'fail': 1, 'timeout': 4}}}}))
            excluded = prepare.prepare(directory, summary, root / 'excluded', state_cache=True)
            self.assertEqual(excluded['counts'], {'excluded': 1})
            included = prepare.prepare(directory, summary, root / 'included',
                                       state_cache=True, include_failing=True)
            entry = included['submissions'][0]
            self.assertEqual(entry['kind'], 'state-cache-only')
            self.assertTrue(entry['state_cache_audited'])
            self.assertIn('__must_state_cache__ = "pure-value-v1"',
                          Path(entry['variant']).read_text())
            self.assertEqual((submission / 'broadcast.py').read_text(), source)
            (submission / 'broadcast.py').write_text(source + '# changed\n')
            changed = prepare.prepare(directory, summary, root / 'changed',
                                      state_cache=True, include_failing=True)
            self.assertEqual(changed['counts'], {'manual_review': 1})

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
    def test_sender_noops_keep_new_sender_and_counter_updates(self):
        api = load_module('anysystem', ROOT / 'crates/must-python/src/anysystem.py')
        cases = {
            'dervis_maksim_v': ('BCAST', {'source': '0', 'seqno': 0, 'text': 'x',
                                       'last_delivered': {'0': -1, '1': -1, '2': -1}}),
            'ibragimov_artem_r': ('BCAST', {'text': 'x'}),
            'dralina_elizaveta_m': ('ECHO', {'id': [1, '0', 'x'], 'text': 'x'}),
            'shilyaev_ivan_p': ('BCAST', {'id': ['0', 1], 'text': 'x',
                                        'v': {'0': 1, '1': 0, '2': 0}}),
        }
        for name, (kind, data) in cases.items():
            with self.subTest(submission=name):
                module = load_module('_sender_edges_' + name, CORPUS / name / 'broadcast.py')
                process = module.BroadcastProcess('0', ['0', '1', '2'])
                predicate = compile(prepare.RULES[name]['predicate'], '<predicate>', 'eval')

                def accepts(sender):
                    return eval(predicate, {**module.__dict__, 'self': process,
                                            'msg': api.Message(kind, data), 'sender': sender})

                def receive(sender):
                    process.on_message(api.Message(kind, data), sender, api.Context(None))

                self.assertTrue(accepts('0'), 'first contact must be accepted')
                receive('0')
                if name == 'shilyaev_ivan_p':
                    # Its conservative guard deliberately waits for delivery.
                    self.assertTrue(accepts('0'))
                    receive('1')
                self.assertFalse(accepts('0'), 'recorded duplicate must be rejected')
                if name in ('dervis_maksim_v', 'ibragimov_artem_r', 'dralina_elizaveta_m'):
                    self.assertTrue(accepts('1'), 'new quorum member must be accepted')
                    receive('1')
                if name in ('dralina_elizaveta_m', 'shilyaev_ivan_p'):
                    self.assertTrue(accepts('2'), 'new sender changes state even after delivery')
                    receive('2')
                    self.assertFalse(accepts('2'))
                self.assertFalse(accepts('0'), 'delivery must preserve rejection')

        name = 'rodionov_valeriy_v'
        module = load_module('_counter_edges', CORPUS / name / 'broadcast.py')
        process = module.BroadcastProcess('0', ['0', '1', '2'])
        predicate = compile(prepare.RULES[name]['predicate'], '<predicate>', 'eval')
        for kind in ('BCAST', 'ACK', 'ACK', 'ACK'):
            msg = api.Message(kind, {'text': 'x'})
            self.assertTrue(eval(predicate, {**module.__dict__, 'self': process, 'msg': msg}))
            process.on_message(msg, '0', api.Context(None))
        self.assertEqual(process._count['x'], 3, 'ACK counts must never be saturated')
        self.assertFalse(eval(predicate, {**module.__dict__, 'self': process,
                                         'msg': api.Message('BCAST', {'text': 'x'})}))

    @unittest.skipUnless(CORPUS.exists(), 'optional local submission corpus absent')
    def test_koptev_queued_bcast_is_noop_but_rebcast_keeps_counting(self):
        api = load_module('anysystem', ROOT / 'crates/must-python/src/anysystem.py')
        name = 'koptev_dmitriy_p'
        module = load_module('_koptev_duplicate', CORPUS / name / 'broadcast.py')
        process = module.BroadcastProcess('0', ['0', '1', '2'])
        predicate = compile(prepare.RULES[name]['predicate'], '<predicate>', 'eval')
        data = {'author': '0', 'sn': 1, 'text': 'x', 'v': {'0': 1, '1': 0, '2': 0}}

        def accepts(kind):
            return eval(predicate, {**module.__dict__, 'self': process,
                                    'msg': api.Message(kind, data)})

        self.assertTrue(accepts('BCAST'))
        process.on_message(api.Message('BCAST', data), '0', api.Context(None))
        self.assertFalse(accepts('BCAST'))
        before = pickle.dumps(process.__dict__)
        ctx = api.Context(None)
        process.on_message(api.Message('BCAST', data), '1', ctx)
        self.assertEqual(pickle.dumps(process.__dict__), before)
        self.assertEqual(ctx._actions(), [])
        process.on_local_message(api.Message('SEND', {'text': 'other'}), api.Context(None))
        self.assertFalse(accepts('BCAST'), 'local callback preserves fixed point')
        for count in (1, 2):
            self.assertTrue(accepts('REBCAST'))
            ctx = api.Context(None)
            process.on_message(api.Message('REBCAST', data), '1', ctx)
            if count == 1:
                self.assertEqual(process._queue[('0', 1)].n_acks, 1)
                self.assertEqual(ctx._actions(), [])
            else:
                self.assertEqual(process._v['0'], 1)
                self.assertNotIn(('0', 1), process._queue)
                self.assertEqual([action['op'] for action in ctx._actions()], ['local'])
            self.assertFalse(accepts('BCAST'))
        self.assertFalse(accepts('REBCAST'), 'delivered frontier takes over rejection')

    @unittest.skipUnless(CORPUS.exists(), 'optional local submission corpus absent')
    def test_zodorov_only_rejects_permanent_foreign_stale_entries(self):
        api = load_module('anysystem', ROOT / 'crates/must-python/src/anysystem.py')
        name = 'zodorov_adam_a'
        module = load_module('_zodorov_stale', CORPUS / name / 'broadcast.py')
        process = module.BroadcastProcess('0', ['0', '1', '2'])
        predicate = compile(prepare.RULES[name]['predicate'], '<predicate>', 'eval')
        data = {'id': ['1', 1], 'text': 'x', 'v': {'0': 0, '1': 1, '2': 0}}

        def accepts(sender):
            return eval(predicate, {**module.__dict__, 'self': process,
                                    'msg': api.Message('BCAST', data), 'sender': sender})

        self.assertTrue(accepts('1'))
        process.on_message(api.Message('BCAST', data), '1', api.Context(None))
        self.assertEqual(process._v['1'], 1)
        self.assertNotIn(('1', 1), process._hold_back)
        self.assertTrue(accepts('1'), 'first delivered duplicate recreates state')
        process.on_message(api.Message('BCAST', data), '1', api.Context(None))
        self.assertIn(('1', 1), process._hold_back)
        self.assertFalse(accepts('1'), 'later duplicate is a permanent stale-entry noop')
        before = pickle.dumps(process.__dict__)
        ctx = api.Context(None)
        process.on_message(api.Message('BCAST', data), '1', ctx)
        self.assertEqual(pickle.dumps(process.__dict__), before)
        self.assertEqual(ctx._actions(), [])
        self.assertTrue(accepts('2'), 'new sender still changes ACK state')
        process.on_message(api.Message('BCAST', data), '2', api.Context(None))
        self.assertFalse(accepts('2'))
        process.on_local_message(api.Message('SEND', {'text': 'local'}), api.Context(None))
        self.assertFalse(accepts('1'))
        later = {'id': ['1', 2], 'text': 'later', 'v': {'0': 0, '1': 2, '2': 0}}
        process.on_message(api.Message('BCAST', later), '1', api.Context(None))
        self.assertEqual(process._v['1'], 2)
        self.assertFalse(accepts('1'), 'advancing frontier cannot revive a stale entry')

    @unittest.skipUnless(CORPUS.exists(), 'optional local submission corpus absent')
    def test_observable_stutter_is_opt_in_and_hash_pinned(self):
        name = 'agafonov_artem_a'
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            directory = root / 'original'
            submission = directory / name
            submission.mkdir(parents=True)
            original = (CORPUS / name / 'broadcast.py').read_bytes()
            (submission / 'broadcast.py').write_bytes(original)
            baseline = root / 'baseline.json'
            baseline.write_text(json.dumps({'submissions': {name: {
                'passed': False, 'counts': {'timeout': 1}}}}))
            default = prepare.prepare(directory, baseline, root / 'default')
            self.assertEqual(default['counts'], {'not_applicable': 1})
            selected = prepare.prepare(directory, baseline, root / 'selected', observable_stutter=True)
            self.assertEqual(selected['submissions'][0]['kind'], 'observable-stutter')
            (submission / 'broadcast.py').write_bytes(original + b'\n# changed\n')
            changed = prepare.prepare(directory, baseline, root / 'changed', observable_stutter=True)
            self.assertEqual(changed['counts'], {'manual_review': 1})
            self.assertEqual((CORPUS / name / 'broadcast.py').read_bytes(), original)

    @unittest.skipUnless(CORPUS.exists(), 'optional local submission corpus absent')
    def test_driver_contract_is_explicit_and_rejects_wrong_node_ids(self):
        api = load_module('anysystem', ROOT / 'crates/must-python/src/anysystem.py')
        name = 'blokhtin_nikita_a'
        source = (CORPUS / name / 'broadcast.py').read_text()
        module = {}
        rule = prepare.DRIVER_CONTRACT_RULES[name]
        exec(prepare.adapted_source(source, rule['predicate'], True, True), module)
        for ids in (['0', '1'], ['0', '1', '10'], ['0', '0', '1']):
            with self.subTest(ids=ids), self.assertRaisesRegex(ValueError, 'process IDs'):
                module['BroadcastProcess']('0', ids).on_start(api.Context(None))
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            original = root / 'original' / name
            original.mkdir(parents=True)
            (original / 'broadcast.py').write_text(source)
            baseline = root / 'baseline.json'
            baseline.write_text(json.dumps({'submissions': {name: {
                'passed': False, 'counts': {'timeout': 1}}}}))
            default = prepare.prepare(original.parent, baseline, root / 'default')
            self.assertEqual(default['counts'], {'not_applicable': 1})
            selected = prepare.prepare(original.parent, baseline, root / 'selected',
                                       broadcast_driver_contract=True)
            entry = selected['submissions'][0]
            self.assertEqual(entry['kind'], 'driver-contract-exact-noop')
            self.assertEqual(entry['assumptions'], prepare.DRIVER_CONTRACT_ASSUMPTIONS)
            self.assertIn('globally distinct', ' '.join(entry['assumptions']))

    @unittest.skipUnless(CORPUS.exists(), 'optional local submission corpus absent')
    def test_shilyaev_cache_requires_explicit_two_broadcast_contract(self):
        name = 'shilyaev_ivan_p'
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            original = root / 'original' / name
            original.mkdir(parents=True)
            source = (CORPUS / name / 'broadcast.py').read_bytes()
            (original / 'broadcast.py').write_bytes(source)
            baseline = root / 'baseline.json'
            baseline.write_text(json.dumps({'submissions': {name: {
                'passed': False, 'counts': {'timeout': 1}}}}))
            generic = prepare.prepare(original.parent, baseline, root / 'generic', state_cache=True)
            self.assertFalse(generic['submissions'][0]['state_cache_audited'])
            selected = prepare.prepare(original.parent, baseline, root / 'selected', state_cache=True,
                                       broadcast_driver_contract=True)
            entry = selected['submissions'][0]
            self.assertTrue(entry['state_cache_audited'])
            self.assertIn('at most two', ' '.join(entry['state_cache_assumptions']).lower())
            self.assertIn('__must_state_cache__ = "pure-value-v1"', Path(entry['variant']).read_text())
            (original / 'broadcast.py').write_bytes(source + b'\n# changed\n')
            changed = prepare.prepare(original.parent, baseline, root / 'changed', state_cache=True,
                                      broadcast_driver_contract=True)
            self.assertEqual(changed['counts'], {'manual_review': 1})

    @unittest.skipUnless(CORPUS.exists(), 'optional local submission corpus absent')
    def test_akimov_stale_guard_preserves_wrong_outer_id_delivery_mark(self):
        api = load_module('anysystem', ROOT / 'crates/must-python/src/anysystem.py')
        name = 'akimov_artem_m'
        module = load_module('_akimov_outer_id', CORPUS / name / 'broadcast.py')
        process = module.BroadcastProcess('2', ['0', '1', '2'])
        rule = prepare.OBSERVABLE_STUTTER_RULES[name]
        predicate = compile(rule['predicate'], '<predicate>', 'eval')
        blocked = {'author': '0', 'msg_id': '1', 'text': 'blocked',
                   'vector_clock': {'0': 1, '1': 2, '2': 0}}
        first = {'author': '1', 'msg_id': '1', 'text': 'first',
                 'vector_clock': {'0': 0, '1': 1, '2': 0}}
        second = {'author': '1', 'msg_id': '2', 'text': 'second',
                  'vector_clock': {'0': 0, '1': 2, '2': 0}}
        for data in (blocked, first, second):
            for sender in ('0', '1'):
                process.on_message(api.Message('BCAST', data), sender, api.Context(None))
        # Delivering blocked under the second callback records outer ID 2 for author 0.
        self.assertEqual(process._delivered_messages['0'], ['2'])
        self.assertEqual(process._vector_clock['0'], 1)
        stale = api.Message('BCAST', blocked)
        self.assertFalse(eval(predicate, {**module.__dict__, 'self': process,
                                         'msg': stale, 'sender': '2'}))
        before_marks = copy.deepcopy(process._delivered_messages)
        ctx = api.Context(None)
        process.on_message(stale, '2', ctx)
        self.assertEqual(ctx._actions(), [])
        self.assertEqual(process._delivered_messages, before_marks)
        self.assertEqual(process._received_messages['0']['1'], ['0', '1', '2'])
        self.assertTrue(any(msg['author'] == '0' and msg['msg_id'] == '1'
                            for msg in process._messages_queue))
        # Stale first contact must still relay: the guard requires a nonempty record.
        fresh_process = module.BroadcastProcess('2', ['0', '1', '2'])
        fresh_process._vector_clock['0'] = 1
        self.assertTrue(eval(predicate, {**module.__dict__, 'self': fresh_process,
                                        'msg': api.Message('BCAST', blocked), 'sender': '0'}))

    @unittest.skipUnless(CORPUS.exists(), 'optional local submission corpus absent')
    def test_akimov_queued_quorum_preserves_first_copy_and_wrong_outer_id(self):
        api = load_module('anysystem', ROOT / 'crates/must-python/src/anysystem.py')
        name = 'akimov_artem_m'
        path = CORPUS / name / 'broadcast.py'
        module = load_module('_akimov_queued_quorum', path)
        rule = prepare.OBSERVABLE_STUTTER_RULES[name]
        variant = dict(module.__dict__)
        exec(prepare.adapted_source(path.read_text(), rule['predicate'], True), variant)
        original = module.BroadcastProcess('2', ['0', '1', '2'])
        adapter = variant['BroadcastProcess']('2', ['0', '1', '2'])
        first = {'author': '0', 'msg_id': '1', 'text': 'first',
                 'vector_clock': {'0': 1, '1': 0, '2': 0}}
        second = {'author': '0', 'msg_id': '2', 'text': 'second',
                  'vector_clock': {'0': 2, '1': 0, '2': 0}}
        for data, sender in [(second, '0'), (second, '1'), (second, '2'),
                             (first, '0'), (first, '1')]:
            contexts = [api.Context(None), api.Context(None)]
            msg = api.Message('BCAST', data)
            original.on_message(msg, sender, contexts[0])
            accept = adapter._must_accept(msg, sender)
            if data is second:
                self.assertEqual(accept, sender != '2')
            if accept:
                adapter.on_message(api.Message('BCAST', data), sender, contexts[1])
            self.assertEqual(contexts[0]._actions(), contexts[1]._actions())
            self.assertEqual(original._vector_clock, adapter._vector_clock)
            self.assertEqual(original._delivered_messages, adapter._delivered_messages)
            if data is second and sender == '2':
                self.assertEqual(len(original._messages_queue), 2)
                self.assertEqual(len(adapter._messages_queue), 1)
        # First drains second, but the unchanged handler marks outer ID 1 only.
        self.assertEqual(adapter._vector_clock['0'], 2)
        self.assertEqual(adapter._delivered_messages, {'0': ['1']})
        self.assertEqual(adapter._messages_queue, [])
        self.assertEqual(len(original._messages_queue), 1)  # stale duplicate second
        self.assertFalse(adapter._must_accept(api.Message('BCAST', second), '2'))

    @unittest.skipUnless(CORPUS.exists(), 'optional local submission corpus absent')
    def test_observable_stutter_coupled_continuations_and_crash_cuts(self):
        api = load_module('anysystem', ROOT / 'crates/must-python/src/anysystem.py')
        # Small quorums, ordinary/reordered traffic, and both early/late crash cuts.
        scenarios = [(1, None), (2, None), (3, None), (3, 3), (5, 18)]
        observations = {}
        for name, rule in {**prepare.OBSERVABLE_STUTTER_RULES, **prepare.DRIVER_CONTRACT_RULES}.items():
            path = CORPUS / name / 'broadcast.py'
            self.assertEqual(prepare.hashlib.sha256(path.read_bytes()).hexdigest(), rule['sha256'])
            module = load_module('_stutter_' + name, path)
            variant = dict(module.__dict__)
            driver_contract = name in prepare.DRIVER_CONTRACT_RULES
            exec(prepare.adapted_source(path.read_text(), rule['predicate'],
                                       rule.get('sender_aware', False), driver_contract), variant)
            rejected = 0
            for size, crash_cut in ([(3, None), (3, 0), (3, 3), (3, 9), (3, 18)]
                                    if driver_contract else scenarios):
                for seed in range(8):
                    with self.subTest(submission=name, size=size, crash=crash_cut, seed=seed):
                        rng = random.Random(seed)
                        ids = list(map(str, range(size)))
                        originals = [module.BroadcastProcess(pid, ids) for pid in ids]
                        adapted = [variant['BroadcastProcess'](pid, ids) for pid in ids]
                        pending = []
                        old_rejections = [dict() for _ in ids]
                        crashed = set()

                        def normalized(process):
                            state = copy.deepcopy(process.__dict__)
                            if name == 'akimov_artem_m':
                                queued_ids = {(queued['author'], queued['msg_id'])
                                              for queued in state['_messages_queue']}
                                for author, records in state['_received_messages'].items():
                                    for msg_id, holders in records.items():
                                        if holders and int(msg_id) <= state['_vector_clock'][author]:
                                            records[msg_id] = ['<seen>']
                                        elif ((author, msg_id) in queued_ids
                                              and len(holders) * 2 >= size):
                                            records[msg_id] = ['<quorum>']
                                queue = []
                                first_copies = {}
                                for queued in state['_messages_queue']:
                                    if queued['vector_clock'][queued['author']] <= state['_vector_clock'][queued['author']]:
                                        continue
                                    key = (queued['author'], queued['msg_id'])
                                    if key in first_copies:
                                        # Source-produced IDs fix all payload fields; do
                                        # not hide distinct payloads or distinct-ID order.
                                        self.assertEqual(queued.type, first_copies[key].type)
                                        self.assertEqual(queued._data, first_copies[key]._data)
                                    else:
                                        first_copies[key] = queued
                                        queue.append(queued)
                                state['_messages_queue'] = queue
                            elif name == 'zodorov_adam_a':
                                stale = {mid for mid in state['_received'] if mid[1] <= state['_v'][mid[0]]}
                                for mid in stale:
                                    state['_acks'].pop(mid, None)
                                    state['_hold_back'].pop(mid, None)
                            elif name == 'dervis_maksim_v':
                                for queued in state['_undelivered']:
                                    if len(set(queued['got_from'])) >= size // 2 + 1:
                                        queued._data['got_from'] = ['<quorum>']
                            elif name == 'koptev_dmitriy_p':
                                for queued in state['_queue'].values():
                                    queued.n_acks = min(queued.n_acks, size // 2 + 1)
                            elif name == 'shilyaev_ivan_p':
                                for mid in state['_delivered']:
                                    state['_gotten'].pop(mid, None)
                            elif not driver_contract:
                                field = {'agafonov_artem_a': '_received_message_counter',
                                         'khamzin_ramil_d': '_delivered',
                                         'rodionov_valeriy_v': '_count'}[name]
                                threshold = process._need if name == 'khamzin_ramil_d' else size // 2 + 1
                                state[field] = {key: min(value, threshold)
                                                for key, value in state[field].items()}
                            def values(value):
                                # Wire-value semantics exclude shim allocation identities.
                                if isinstance(value, api.Message):
                                    return (value.type, values(value._data))
                                if name == 'koptev_dmitriy_p' and isinstance(value, (module.MessageState, variant['MessageState'])):
                                    return values(value.__dict__)
                                if isinstance(value, dict):
                                    # Dict traversal order can affect future delivery order.
                                    return tuple((key, values(item)) for key, item in value.items())
                                if isinstance(value, list):
                                    return [values(item) for item in value]
                                if isinstance(value, tuple):
                                    return tuple(values(item) for item in value)
                                return value
                            return values(state)

                        def callback(destination, kind, wire, sender=None):
                            nonlocal rejected
                            original, adapter = originals[destination], adapted[destination]
                            contexts = [api.Context(None), api.Context(None)]
                            before = normalized(adapter)
                            accept = True
                            if kind == 'network':
                                msg = api.Message.from_json(wire['kind'], wire['data'])
                                accept = (adapter._must_accept(msg, sender) if rule.get('sender_aware')
                                          else adapter._must_accept(msg))
                                original.on_message(msg, sender, contexts[0])
                                if accept:
                                    adapter.on_message(api.Message.from_json(wire['kind'], wire['data']), sender, contexts[1])
                                else:
                                    rejected += 1
                                    old_rejections[destination][(sender, wire['kind'], wire['data'])] = wire
                                    self.assertEqual(normalized(adapter), before)
                                    self.assertEqual(contexts[0]._actions(), [])
                            else:
                                for process, ctx in zip((original, adapter), contexts):
                                    process.on_local_message(api.Message('SEND', {'text': wire}), ctx)
                            self.assertEqual(contexts[0]._actions(), contexts[1]._actions())
                            self.assertEqual(normalized(original), normalized(adapter))
                            for (old_sender, _, _), old in old_rejections[destination].items():
                                old_msg = api.Message.from_json(old['kind'], old['data'])
                                if rule.get('sender_aware'):
                                    self.assertFalse(adapter._must_accept(old_msg, old_sender))
                                else:
                                    self.assertFalse(adapter._must_accept(old_msg))
                            for action in contexts[0]._actions():
                                if action['op'] == 'send':
                                    pending.append((str(destination), int(action['to']), action['message']))

                        for i, (original, adapter) in enumerate(zip(originals, adapted)):
                            original.on_start(api.Context(None))
                            adapter.on_start(api.Context(None))
                        # Repeated text tests Khamzin/Rodionov key collisions; other IDs remain fresh.
                        callback(0, 'local', 'first' if driver_contract else 'same')
                        if name != 'shilyaev_ivan_p':
                            callback(0, 'local', 'second' if driver_contract else 'same')
                        callback(size - 1, 'local', 'other')
                        for step in range(256):
                            if crash_cut == step:
                                crashed.add(size - 1)
                            if not pending:
                                break
                            sender, destination, wire = pending.pop(rng.randrange(len(pending)))
                            if destination not in crashed:
                                callback(destination, 'network', wire, sender)
                            if step == 9 and 0 not in crashed and name != 'shilyaev_ivan_p':
                                callback(0, 'local', 'continuation')
            self.assertGreater(rejected, 0, name)
            observations[name] = rejected
        print('Coupled observable-stutter rejections:', observations)

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
                        accept = eval(predicate, {**module.__dict__, 'self': process, 'msg': msg, 'sender': sender})
                        self.assertEqual(pickle.dumps(process.__dict__), before,
                                         f'{name}: predicate mutates process')
                        ctx = api.Context(None)
                        process.on_message(msg, sender, ctx)
                        if not accept:
                            rejected += 1
                            permanently_rejected[destination][(sender, wire['kind'], wire['data'])] = (sender, wire)
                            self.assertEqual(ctx._actions(), [], f'{name}: skipped output')
                            self.assertEqual(pickle.dumps(process.__dict__), before,
                                             f'{name}: skipped state mutation')
                        commit(str(destination), ctx)
                        for previous_sender, previous in permanently_rejected[destination].values():
                            old_msg = api.Message.from_json(previous['kind'], previous['data'])
                            self.assertFalse(eval(predicate, {**module.__dict__, 'self': process,
                                                              'msg': old_msg, 'sender': previous_sender}),
                                             f'{name}: rejected message became relevant again')
                observations[name] = rejected
                if name in {'dervis_maksim_v', 'ibragimov_artem_r', 'rodionov_valeriy_v',
                            'dralina_elizaveta_m', 'shilyaev_ivan_p', 'koptev_dmitriy_p',
                            'zodorov_adam_a'}:
                    self.assertGreater(rejected, 0, 'new audit must exercise reachable rejections')
        print('Sampled rejected callbacks:', json.dumps(observations, sort_keys=True))


if __name__ == '__main__':
    unittest.main()
