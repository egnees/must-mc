#!/usr/bin/env python3
"""Prepare separately labelled, audited selective-receive submission variants."""

import argparse
import ast
from collections import Counter
import hashlib
import json
from pathlib import Path
import shutil


RULES = {'afonkin_pavel_v': {'kind': 'exact-return',
                     'predicate': "msg.type != 'ACK' or (msg['sn'], msg['sender']) not in "
                                  "self._recived_messages or (msg['sn'], msg['sender']) in "
                                  'self._waiting_for_ack',
                     'reason': 'Reject only post-majority ACK: already received and no longer '
                               'waiting. Early ACK stays accepted.',
                     'sha256': '060551b1ff4a4d770b7150beb6a6eda1847797ed0bd935ec570c70ad452a1599'},
 'akimov_artem_m': {'kind': 'exact-return',
                    'predicate': "msg.type != 'BCAST' or msg['author'] not in "
                                 "self._delivered_messages or msg['msg_id'] not in "
                                 "self._delivered_messages[msg['author']]",
                    'reason': 'Existing outer delivered guard skips the entire handler body.',
                    'sha256': '48850feb5f5585f0378e92c2f5cb3cd5c72fa5601914819fe692918ee6481770'},
 'anikeev_ilya_a': {'kind': 'exact-return',
                    'predicate': "msg.type != MessageTypes.BROADCAST or msg['id'] not in "
                                 'self._delivered_ids',
                    'reason': 'Existing delivered-id early return.',
                    'sha256': '9be5376c6705a5a980e549dd1f3847a0438f10225661051bbf6345072dd91f64'},
 'asadullin_aydar_m': {'kind': 'exact-return',
                       'predicate': "msg.type != 'BCAST' or tuple(msg['id']) not in "
                                    'self._delivered',
                       'reason': 'Existing delivered-id early return.',
                       'sha256': '887d3e14ef68e09aa1194c1a780d9a61dbd03084fbf7765aebf623b5a4988948'},
 'baydakov_kirill_a': {'kind': 'exact-return',
                       'predicate': "msg.type != 'BCAST' or msg['id'] not in self._got_acks or "
                                    "len(self._got_acks[msg['id']]) != len(self._processes) // 2",
                       'reason': 'Inline pure deliver_acks_cond from existing early return.',
                       'sha256': '8df62b14c33d8eaf725b5ebe4e4f9ab3249cdb039f9a511f2c49196d3ccd94cd'},
 'chernov_timofey_i': {'kind': 'exact-return',
                       'predicate': "msg.type != 'ACK' or msg['text'] not in self._ignore",
                       'reason': 'Existing ACK early return; BCAST still generates ACK broadcasts.',
                       'sha256': '689da67c66411ac0be3fa3969f586b6603681085dbe04beaa137dede7c2c7161'},
 'dervis_maksim_v': {'kind': 'exact-return',
                     'predicate': "msg.type != 'BCAST' or msg['seqno'] > "
                                  "self._last_delivered[msg['source']]",
                     'reason': 'is_already_delivered only reads sequence/frontier; preceding pnt '
                               'is pass.',
                     'sha256': '51ea5143cf309787c6ca88798bda58138e73d50b342f37c3e0538cb45bbd1c96'},
 'drugov_maksim_i': {'kind': 'exact-return',
                     'predicate': "msg.type != 'BCAST' or msg['text'] not in self._delivered",
                     'reason': 'Existing delivered-text early return.',
                     'sha256': 'ba397a1557c843e1b44e9ce0a4751f9c6192634706b507b5b96e5451e39dd509'},
 'gusev_egor_d': {'kind': 'exact-return',
                  'predicate': "msg.type != 'DATA' or (msg['sender'], int(msg['sn'])) not in "
                               "self.buf or (msg['sender'], int(msg['sn'])) not in self.seen or "
                               "(msg['sender'], int(msg['sn'])) not in self.rdy_s or "
                               "(msg['sender'], int(msg['sn'])) not in self.deliv",
                  'reason': 'DATA skips both initialization branches and try_rdy/try_del return '
                            'immediately when buf, seen, ready-sent and delivered contain the ID; '
                            'all four memberships persist. ECHO and READY remain accepted.',
                  'sha256': '93df222b211cb14027a979fae2fdfb7cdb9f59367134c11474206b12127bdfd0'},
 'keropyan_artur_a': {'kind': 'exact-return',
                      'predicate': "msg.type not in ('BCAST', 'ECHO', 'READY') or "
                                   "self.delivered_up_to[self.idx_of[msg['orig']]] < "
                                   "int(msg['seq'])",
                      'reason': 'Existing delivered frontier return precedes echo, ready, nudge '
                                'and drain.',
                      'sha256': '0c5ddef975bb9e3efa99ccd41269bb4e349064081ef8acfe36acfd379074283a'},
 'konoplev_nikita_s': {'kind': 'exact-return',
                       'predicate': "msg.type != 'BCAST' or tuple(msg['msg_id']) not in "
                                    'self._delivered_msg',
                       'reason': 'Existing early return before state mutation or output; other '
                                 'message types remain accepted.',
                       'sha256': '08c4534cbb0ff0ea53760a79a2f285af5b4c75a8a2ec0b9db4ab8dc9347a599e'},
 'konovalov_artem_yu': {'kind': 'exact-return',
                        'predicate': "msg.type != 'BCAST' or msg['dpp'][msg['id']] > "
                                     "self._delivered_per_proc[msg['id']]",
                        'reason': 'Existing early return before state mutation or output; other '
                                  'message types remain accepted.',
                        'sha256': '2965f5e0fd86d8c82411c4b40d81100155ef22dc362afe47391aad4fec2e13f3'},
 'koptev_dmitriy_p': {'kind': 'exact-return',
                      'predicate': "msg['sn'] > self._v[msg['author']]",
                      'reason': 'Existing early return before state mutation or output; other '
                                'message types remain accepted.',
                      'sha256': '53083ff086055a12d1db88230f79db500ed15ea84147049bdc6ca0784952a5d0'},
 'krivetskiy_ilya_a': {'kind': 'exact-return',
                       'predicate': "msg.type != 'BCAST' or msg['msg_id'] not in self.delivered",
                       'reason': 'Existing early return before state mutation or output; other '
                                 'message types remain accepted.',
                       'sha256': '3fce4efee31dd045bb3052f1176fed18c7b9ff49267765b4e5b943e93a80db70'},
 'latyshev_ivan_s': {'kind': 'exact-return',
                     'predicate': "msg.type not in ('BCAST', 'ECHO', 'READY') or "
                                  "self.delivered[self.pid2idx[msg['orig']]] < int(msg['seq'])",
                     'reason': 'Existing early return before state mutation or output; other '
                               'message types remain accepted.',
                     'sha256': 'fa61f638024266fcbdd93d425e58fafad6f898e9af0832025420fcc016cc6f04'},
 'lubsanov_dmitriy_a': {'kind': 'exact-return',
                        'predicate': "msg.type != 'BCAST' or msg['cnt'] not in self._delivered",
                        'reason': 'Existing early return before state mutation or output; other '
                                  'message types remain accepted.',
                        'sha256': '1ad52f7989520df2003946a2725f4a62364165960648fb5df96ee2ae58c89d2b'},
 'makhlin_miron_yu': {'kind': 'exact-noop',
                      'predicate': "msg.type != 'CONFIRM' or msg['text'] not in self._final_sent "
                                   "or msg['confirm_author'] not in "
                                   "self._confirmed.get(msg['text'], set())",
                      'reason': 'After final_sent, duplicate CONFIRM from an already recorded '
                                'confirm_author performs only idempotent set.add; no state change '
                                'or output. Both memberships persist.',
                      'sha256': '5784c6c7b3191c4874b58deec5017c830a666492badb1ef8a3a3131a27b16fe1'},
 'malkov_maksim_l': {'kind': 'exact-return',
                     'predicate': "msg.type != 'ACK' or msg['text'] not in self._urb_msgs_acks or "
                                  "self._urb_msgs_acks[msg['text']] <= len(self._processes)",
                     'reason': 'Only the existing permanent ACK lock return after delivery; early '
                               'ACK with absent record remains accepted and is discarded by the '
                               'original handler.',
                     'sha256': 'd16bf02cb8141857dd179a49040955451e307da6c9f86b7db997550ef9d165ff'},
 'myshak_roman_v': {'kind': 'exact-noop',
                    'predicate': "msg.type != 'DELIVER_BCAST' or (msg['id'], msg['No']) not in "
                                 "self._records or not self._records[(msg['id'], "
                                 "msg['No'])]['cry_about_it'] or not self._records[(msg['id'], "
                                 "msg['No'])]['delivered'] or not "
                                 "set(self._processes).issubset(self._records[(msg['id'], "
                                 "msg['No'])]['aware'])",
                    'reason': 'DELIVER_BCAST after relay+delivery with every possible sender '
                              'already aware performs only idempotent set.add; both guarded '
                              'effects are permanently disabled. FIRST_BCAST remains accepted.',
                    'sha256': 'ec7116cafbc2818db8fd8abacf2b2e9fd0943a4a6fc30e50b7ed8a4e71f120f7'},
 'nesteruk_vladislav_o': {'kind': 'exact-return',
                          'predicate': "msg.type != 'BCAST' or int(msg['id'].split('_')[2]) not in "
                                       "self._need_to_deliver.get(int(msg['id'].split('_')[1]), "
                                       '{})',
                          'reason': 'Existing early return before state mutation or output; other '
                                    'message types remain accepted.',
                          'sha256': 'c49fceeab76e74cc9a360d3b04d751f80d00b962d83cc11d0b2c6f33bbd52b9f'},
 'neykov_daniil_d': {'kind': 'exact-return',
                     'predicate': "msg.type != 'BCAST' or make_msg_id(msg['text'], msg['origin'], "
                                  "msg['clock']) not in self._acks_by_msg",
                     'reason': 'Existing permanent no-op branch; delivered/seen markers or '
                               'frontiers are monotonic.',
                     'sha256': 'e21122794ddfcc8fe4cac7516b11aeba58d25998dd2451b4a056df2815759944'},
 'panov_andrey_v': {'kind': 'exact-return',
                    'predicate': "msg.type != 'BCAST' or (msg['text'], msg['origin'], "
                                 "tuple(sorted(msg['clock'].items()))) not in self._acked",
                    'reason': 'Existing permanent no-op branch; delivered/seen markers or '
                              'frontiers are monotonic.',
                    'sha256': '23e09333c67597038bbee4c53ce204a6ddfceefe43b3d3299f98693b49f5b83c'},
 'plakhuta_aleksey_a': {'kind': 'exact-return',
                        'predicate': "(msg['parent'], msg['id'], msg['text']) not in "
                                     'self._delivered',
                        'reason': 'Existing early return before state mutation or output; other '
                                  'message types remain accepted.',
                        'sha256': '6b5628dcaed32e32e1fa672f0bb4cedd60adb64c10b04428c7de834ecb56e005'},
 'povolotskiy_roman_a': {'kind': 'exact-return',
                         'predicate': "msg.type != 'DONE' or (msg['proc_id'], msg['id']) not in "
                                      'self._got_messages',
                         'reason': 'Existing early return before state mutation or output; other '
                                   'message types remain accepted.',
                         'sha256': 'dfe40d2f2417fc33f245b960f817871220ae65e1ca4507b31f07b45e7c797dc3'},
 'pugachev_dmitriy_v': {'kind': 'exact-return',
                        'predicate': "msg.type != 'BCAST' or msg['stable'] or tuple(msg['msg_id']) "
                                     'not in self._stable',
                        'reason': 'Existing early return before state mutation or output; other '
                                  'message types remain accepted.',
                        'sha256': '92dfa82fadeb292d63df42f997f636eee50954bd12a2cdb6c4d17796e137311f'},
 'sabgir_sofiya_r': {'kind': 'exact-return',
                     'predicate': "msg.type != 'BCAST' or int(msg['msg_id'].split(':')[1]) >= "
                                  "self._delivered_count[msg['msg_id'].split(':')[0]]",
                     'reason': 'Existing sequence-frontier early return.',
                     'sha256': '46ce55c70d4f23c45bced96e1fca83f035c987d56772bee479e4855af72ecbbb'},
 'serebrennikov_dan_n': {'kind': 'exact-return',
                         'predicate': "msg.type != 'BCAST' or (msg['sender'], msg['seq']) not in "
                                      'self._delivered',
                         'reason': 'Only the existing delivered early return; repeated forwarding '
                                   'before delivery remains.',
                         'sha256': 'b484915cce6ff8ac6208427a55927668443363dc844a3ba165a735001c3b68a4'},
 'sevryukov_nikita_v': {'kind': 'exact-return',
                        'predicate': "msg.type != 'BCAST' or "
                                     "msg['causal'].get(msg['original_sender'], 0) > "
                                     "self._causal.get(msg['original_sender'], 0)",
                        'reason': 'Inline existing pure _is_already_deliveried early return.',
                        'sha256': '02a28d846151357ad620d883d5fe63ee5bdfa693fff1140e7816040dc0faef22'},
 'shestakov_vyacheslav_g': {'kind': 'exact-return',
                            'predicate': "msg.type != 'BCAST_PUSH' or (msg['sender'], "
                                         "tuple(msg['prev'])) not in self._msgs_in_local or "
                                         "(msg['sender'], tuple(msg['prev'])) in self._cnt_wait",
                            'reason': 'Existing permanent no-op branch; delivered/seen markers or '
                                      'frontiers are monotonic.',
                            'sha256': '3e8e319f5b7ec6e838c179d57fb6e6aedf682c6f42c162b878033ec2e0484ffa'},
 'shevchenko_budimir_m': {'kind': 'exact-return',
                          'predicate': "msg.type != 'ACK_ACK' or any(value > self._cloak[i] for i, "
                                       "value in enumerate(msg['cloak']))",
                          'reason': 'Existing permanent no-op branch; delivered/seen markers or '
                                    'frontiers are monotonic.',
                          'sha256': '7b3fa13505c37672e8e45199976bca9687dce04b160b9b8058cb2527b36817ae'},
 'shteyn_maksim_m': {'kind': 'exact-return',
                     'predicate': "msg['id'] not in self._received",
                     'reason': 'Existing received-id early return before any mutation.',
                     'sha256': 'c7aa8d328de80cd939c984828c41d92428ce25249531a21a682929289d0ae26c'},
 'shteynman_aleksandr_a': {'kind': 'exact-return',
                           'predicate': "msg.type != BCAST or (msg['sender'], msg['seq']) not in "
                                        'self._received',
                           'reason': 'Existing BCAST early return; ACK remains accepted.',
                           'sha256': 'a59f5a9280383f56d44a2ca58ecb7c3b714424390453304a269b669c27621584'},
 'strazdina_alisa_l': {'kind': 'exact-return',
                       'predicate': "msg.type != 'READY' or msg['text'] not in self._delivered",
                       'reason': 'Existing permanent no-op branch; delivered/seen markers or '
                                 'frontiers are monotonic.',
                       'sha256': 'd772b432dfe9bd7de4786e29ac60bedf025590b61ea7cc6eef486075b6b02391'},
 'van_petr': {'kind': 'exact-return',
              'predicate': "msg.type != 'DATA' or tuple(msg[MSG_ID]) not in self._delivered_msgs "
                           'or tuple(msg[MSG_ID]) not in self._pending_msgs or '
                           'int(msg[MESSAGE_SENDER]) not in '
                           'self._pending_msgs[tuple(msg[MSG_ID])][ACK_SET]',
              'reason': 'Existing permanent no-op branch; delivered/seen markers or frontiers are '
                        'monotonic.',
              'sha256': '1f289d7702959ca62ed172876ff0a80411c344d9aa674e75d1881973cd95805b'},
 'vasilyev_aleksey_l': {'kind': 'exact-return',
                        'predicate': "msg.type != 'BCAST' or "
                                     "msg['times'][self._processes.index(msg['author'])] > "
                                     "self._times[self._processes.index(msg['author'])]",
                        'reason': 'Existing permanent no-op branch; delivered/seen markers or '
                                  'frontiers are monotonic.',
                        'sha256': '70b807f9afd2cbddc261b4c229e46e02d70c4989d93984b01d2b1a90a6c50a00'},
 'veryutina_alina_a': {'kind': 'exact-return',
                       'predicate': "msg.type != 'BCAST' or "
                                    "self.list_of_map_ack[int(msg['sender'])].get(msg['id_msg']) "
                                    "!= -1 or msg['id_msg'] not in "
                                    "self.history[int(msg['sender'])]",
                       'reason': 'Existing permanent no-op branch; delivered/seen markers or '
                                 'frontiers are monotonic.',
                       'sha256': 'fc5ed7f6e119b65e5bd01d006873693737e1786057cb0a43fc86f6f1bf8b1d4a'},
 'vovk_mikhail_a': {'kind': 'exact-return',
                    'predicate': "msg.type != 'ACK' or msg['id'] not in self._delivered or "
                                 "msg['id'] in self._hold_queue",
                    'reason': 'Existing ACK early return only after permanent delivery and queue '
                              'removal; BCAST remains accepted.',
                    'sha256': 'fbf521f4598b31154845098b2c905c4dc63270d16181638d5033359db94796a5'},
 'zavarin_aleksandr_s': {'kind': 'exact-return',
                         'predicate': "msg.type != 'BCAST' or self._delivered[msg['sdr_id']] <= "
                                      "msg['msg_id']",
                         'reason': 'Existing delivered-frontier return; get_merge_id only formats '
                                   'text.',
                         'sha256': '6a0b3990884af7d5c53a4b1b8b441685b26b331f9baa3b6e0fe171294beeed03'}}

NOT_APPLICABLE = {'agafonov_artem_a': 'Each BCAST increments the counter, including after majority.',
 'alekseev_stanislav_m': 'BCAST updates ACK sender state and runs delivery; no message-only '
                         'permanent early return.',
 'andreev_evgeniy_i': 'BCAST updates ACK sender state and rebuilds the buffer even after delivery; '
                      'no permanent early return.',
 'artemov_mikhail_s': 'Each BCAST updates holder state and runs the holdback drain.',
 'artyukhov_dmitriy_a': 'Duplicates still update the holder set.',
 'averin_vadim_v': 'DATA updates senders then runs delivery even after the delivered flag; no '
                   'permanent early return.',
 'belskiy_artem_o': 'Sender set changes before delivered guard; len==1 can trigger repeat relay.',
 'bityukov_pavel_a': 'Each BCAST sends ACK; each ACK updates holder state and drains.',
 'blokhtin_nikita_a': 'check_msg updates transport sender state before duplicate suppression and '
                      'queue processing.',
 'bolotskiy_andrey_s': 'Existing guard compares Message objects to a set of ID strings and never '
                       'rejects network messages.',
 'borchuk_dmitriy_v': 'Every BCAST increments its receive counter, including after the majority '
                      'threshold.',
 'chernyy_anton_l': 'Every BCAST increments _from counter before the majority check.',
 'didenko_kirill_v': 'BCAST adds transport sender to seen_from before delivery guards; no '
                     'permanent no-op guard.',
 'donskoy_dmitriy_v': 'Delivered duplicates first add sender and then replace _seen with a new '
                      'empty set; not an existing mutation-free skip.',
 'eliseev_vladislav_a': 'ACK after majority reinserts the message in _ok_buffer and invokes flush; '
                        'cannot be dropped as a no-op.',
 'eltsov_danil_a': 'Each peer sends this ID once and excludes self; the conservative all-senders '
                   'guard removes no reachable network duplicates.',
 'eremina_kseniya_d': 'BCAST updates ACK sender state and then attempts delivery of every queued '
                      'message.',
 'fominykh_darya_d': 'BCAST adds transport sender before the delivered check.',
 'galimov_denis_r': 'BCAST updates seen_from before delivery drain; no permanent early return.',
 'golov_andrey_e': 'BCAST mutates the input message from_id, updates holder state and runs '
                   'delivery; no mutation-free skip.',
 'gorokhov_dmitriy_a': 'Every BROADCAST increments _messages before threshold checks.',
 'ivanov_maksim_s': 'Stores Message objects in an iterated set; skipping receives may change '
                    'allocation-derived hashes and observable iteration order.',
 'ivanova_arina_v': 'Stores Message objects in an iterated set; skipping receives may change '
                    'allocation-derived hashes and observable iteration order.',
 'kataev_ilya_i': 'Every message updates received_from sender state before delivery drain.',
 'khamzin_ramil_d': 'Duplicate counters are incremented before the early return.',
 'khmura_ivan_a': 'ACK updates sender state; duplicate BCAST still runs global drain. No existing '
                  'unconditional permanent no-op branch.',
 'kholopkin_ilya_v': 'BCAST/ECHO/READY update transport sender sets before ready and delivery '
                     'logic.',
 'kostin_daniil_i': 'A duplicate can recreate pending state after delivery and adds transport '
                    'sender ACK.',
 'kozlov_maksim_a': 'Every BCAST increments ACK count; post-majority processing appends to '
                    'holdback queue.',
 'krivoschekov_andrey_a': 'Every message increments _count before pending and delivery logic.',
 'lazo_arseniy_d': 'Duplicates add transport sender to ACK set and run delivery; no existing '
                   'permanent skip.',
 'nekrasov_stanislav_i': 'Every broadcast increments its receive counter.',
 'nikolaeva_ekaterina_a': 'Existing self-sender guard needs immediate sender, absent from msg-only '
                          'API.',
 'olshevskiy_aleksandr_m': 'Updates holder state and invokes acceptance/drain before any duplicate '
                           'guard.',
 'polivin_nikita_e': 'Overwrites stored payload and adds holder before delivery processing.',
 'polyakov_ivan_a': 'Adds holders before delivery processing; no existing payload-only skip guard.',
 'ponkratov_aleksandr_a': 'Existing-message branch still adds to quorum and invokes delivery.',
 'rempel_dmitriy_a': 'Increments message counter before checking whether payload was already '
                     'stored.',
 'rutkovskiy_aleksey_s': 'Duplicates still increment the ACK counter.',
 'sennov_egor_a': 'Duplicate sender branch requires immediate sender; callback still drains.',
 'shakhdullaeva_karina_d': 'Updates pending payload or echo holder state then invokes delivery.',
 'shevlyakov_fedor_s': 'Updates ACK/READY holder sets before checking readiness.',
 'shilyaev_ivan_p': 'Adds sender before delivered-message return in helper.',
 'shirokovskikh_aleksandr_s': 'Every repeated payload increments the receive counter.',
 'smirnov_gleb_a': 'Duplicates still increment the receive counter.',
 'smirnov_matvey_m': 'Adds relay sender before forwarding/delivery checks.',
 'smirnyagin_artem_k': 'Stores Message objects in an iterated set; skipping receives may change '
                       'allocation-derived hashes and observable iteration order.',
 'sopolev_vladislav_n': 'ACK for unknown payload is only temporarily irrelevant; later buffering '
                        'would change behavior.',
 'stepanov_anton_a': 'Updates message metadata and increments process counter for each BCAST.',
 'stovba_igor_i': 'Updates holder sets and can emit later protocol phases even after payload '
                  'delivery.',
 'titov_fedor_a': 'NET_MESSAGE always replies; CALLBACK updates sender set before processing '
                  'delivery.',
 'trushkova_ekaterina_s': 'Adds sender to ACK set before draining pending deliveries.',
 'tsarapkin_maksim_d': 'Adds sender to message state before processing delivery.',
 'zamyatin_matvey_a': 'Records sender before dispatch; BCAST can send ACK for existing payload.',
 'zodorov_adam_a': 'Updates ACK sets and can recreate holdback entries for old messages.'}

def adapted_source(source, predicate):
    suffix = f'''

_MustOriginalBroadcastProcess = BroadcastProcess


class BroadcastProcess(_MustOriginalBroadcastProcess):
    def _must_accept(self, msg):
        return {predicate}

    def on_start(self, ctx):
        result = super().on_start(ctx)
        ctx.set_predicate(self._must_accept)
        return result

    def on_local_message(self, msg, ctx):
        result = super().on_local_message(msg, ctx)
        ctx.set_predicate(self._must_accept)
        return result

    def on_message(self, msg, sender, ctx):
        result = super().on_message(msg, sender, ctx)
        ctx.set_predicate(self._must_accept)
        return result

    def on_timer(self, name, ctx):
        result = super().on_timer(name, ctx)
        ctx.set_predicate(self._must_accept)
        return result
'''
    result = source + suffix
    ast.parse(result)
    return result


def unsupported_sources(source):
    found = set()
    tree = ast.parse(source)
    random_names = {'random', 'sample', 'randint', 'choice', 'shuffle', 'Random'}
    for node in ast.walk(tree):
        if not isinstance(node, ast.Call):
            continue
        name = ast.unparse(node.func)
        if (name.startswith(('random.', 'time.', 'os.', 'pathlib.'))
                or name in random_names | {'open', 'ctx.set_timer', 'ctx.set_timer_once'}):
            found.add(name)
    return sorted(found)


def prepare(directory, summary_path, output):
    directory, output = directory.resolve(), output.resolve()
    if directory == output or directory in output.parents or output in directory.parents:
        raise ValueError('Output must be separate from the original submissions directory')
    summary = json.loads(summary_path.read_text())
    output.mkdir(parents=True, exist_ok=True)
    entries = []
    for name, baseline in sorted(summary['submissions'].items()):
        counts = baseline['counts']
        if not (baseline['passed'] or counts.get('timeout')):
            continue
        path = directory / name / 'broadcast.py'
        if directory not in path.resolve().parents:
            raise ValueError(f'Submission path escapes corpus: {name}')
        source = path.read_text()
        digest = hashlib.sha256(path.read_bytes()).hexdigest()
        entry = {'submission': name, 'source': str(path), 'sha256': digest,
                 'baseline_counts': counts, 'baseline_passed': baseline['passed']}
        if any(counts.get(key) for key in ('fail', 'error', 'unsupported', 'inconclusive')):
            entry.update(status='excluded', reason='Baseline has a failure or unsupported/error result')
        elif unsupported := unsupported_sources(source):
            entry.update(status='excluded', reason='Needs nondeterminism/timer review', calls=unsupported)
        elif name in NOT_APPLICABLE:
            entry.update(status='not_applicable', reason=NOT_APPLICABLE[name])
        elif name not in RULES:
            entry.update(status='manual_review', reason='No audited predicate; original remains unchanged')
        elif digest != RULES[name]['sha256']:
            entry.update(status='manual_review', reason='Source changed since predicate audit')
        else:
            rule = RULES[name]
            destination = output / 'submissions' / name
            if destination.exists():
                raise ValueError(f'Refusing to overwrite existing variant: {destination}')
            shutil.copytree(path.parent, destination, ignore=shutil.ignore_patterns('__pycache__'))
            variant = destination / 'broadcast.py'
            variant.write_text(adapted_source(source, rule['predicate']))
            entry.update(status='adapted', reason=rule['reason'], kind=rule['kind'],
                         predicate=rule['predicate'], variant=str(variant),
                         variant_sha256=hashlib.sha256(variant.read_bytes()).hexdigest())
        entries.append(entry)
    result = {'baseline': str(summary_path.resolve()), 'corpus': str(directory),
              'counts': dict(Counter(entry['status'] for entry in entries)),
              'submissions': entries}
    (output / 'manifest.json').write_text(json.dumps(result, indent=2, ensure_ascii=False) + '\n')
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('directory', type=Path)
    parser.add_argument('--baseline', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = prepare(args.directory, args.baseline, args.output)
    print(json.dumps(result['counts'], sort_keys=True))


if __name__ == '__main__':
    main()
