"""Offline tests for scripts/coverage: Lean lexical CC, C-codegen filtering, specialization ownership,
loop-clone merging, and CRAP calculation."""
import importlib.machinery
import importlib.util
from pathlib import Path
import unittest

SCRIPTS = Path(__file__).resolve().parents[1]
loader = importlib.machinery.SourceFileLoader('winnow_coverage', str(SCRIPTS / 'coverage'))
spec = importlib.util.spec_from_loader('winnow_coverage', loader)
cov = importlib.util.module_from_spec(spec)
loader.exec_module(cov)


def _reg(line, count, kind=0, fid=0):
    return [line, 1, line, 10, count, fid, 0, kind]


class TestLeanComplexity(unittest.TestCase):
    def test_straight_line_and_proofs_ignored(self):
        src = """
def add (a b : Nat) : Nat := a + b

theorem add_comm (a b : Nat) : add a b = add b a := by
  if a = b then rfl else omega
"""
        fns = cov.analyze_lean_file(src)
        self.assertEqual(len(fns), 1)
        self.assertEqual(fns[0]['name'], 'add')
        self.assertEqual(fns[0]['cc'], 1)

    def test_branches_matches_wildcards_and_or_patterns(self):
        src = """
def classify (x : Nat) (ok : Bool) : Nat :=
  if ok && x > 0 || x == 42 then
    match x with
    | 0 | 1 => 10
    | 2 => 20
    | _ => 30
  else
    0
"""
        # 1 base + if + && + || + (0|1 =>) + (2 =>) = 6 (wildcard `_ =>` is default)
        fns = cov.analyze_lean_file(src)
        self.assertEqual(fns[0]['cc'], 6)

    def test_comments_strings_and_interpolation_blanked(self):
        src = r'''
-- if a && b || c
/- nested /- if unless for -/ while -/
def greet (x' : Bool) : String :=
  let a := "if a && b | x => y"
  let b := r#"unless while repeat"#
  let c := 'a'
  let d := s!"val={if x' then "if && ||" else "ok"}"
  a ++ b ++ toString c ++ d
'''
        # Only the `if` inside the s!"..." interpolation counts -> CC = 2
        # Wait: blanking string interpolation blanks `{...}` too in compare/tools/lean.py!
        fns = cov.analyze_lean_file(src)
        self.assertEqual(fns[0]['name'], 'greet')
        self.assertEqual(fns[0]['cc'], 1)

    def test_lean_imports(self):
        src = """
-- import Fake.Commented
import Winnow.Tx.PSBT
private import Winnow.IO.Base
public import all SecpCt.Field
"""
        self.assertEqual(cov.lean_imports(src), ['Winnow.Tx.PSBT', 'Winnow.IO.Base', 'SecpCt.Field'])


class TestAnalyzeC(unittest.TestCase):
    def test_is_shared_and_structural_duplicates_stripped(self):
        c_lines = """
LEAN_EXPORT lean_object* lp_p_f(lean_object* v_x_1_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
return v_x_1_;
}
else
{
lean_object* v_a_2_; uint8_t v_isSharedCheck_3_;
v_a_2_ = lean_ctor_get(v_x_1_, 0);
v_isSharedCheck_3_ = !lean_is_exclusive(v_x_1_);
if (v_isSharedCheck_3_ == 0)
{
goto v_resetjp_4_;
}
else
{
goto v_resetjp_4_;
}
v_resetjp_4_:
{
if (v_isShared_5_ == 0)
{
goto v_reusejp_6_;
}
else
{
goto v_reusejp_6_;
}
v_reusejp_6_:
{
return v_a_2_;
}
}
}
}
}
""".strip().splitlines()
        skip_s, skip_b = cov.analyze_c_lines(c_lines)
        # Entry (L1) kept; _start (L2), if cond (L4), isSharedCheck cond/then/else (L13,L14,L18),
        # v_resetjp (L21), isShared cond/then/else (L23,L24,L28), v_reusejp (L31) all stripped.
        for ln in (2, 4, 13, 14, 18, 21, 23, 24, 28, 31):
            self.assertIn(ln, skip_s, f'line {ln} ({c_lines[ln-1]}) should be structural-skipped')
        # Real arms: L5 (then) and L9 (else) kept; neither is a bind exit (pure function, no boxed+1)
        self.assertNotIn(5, skip_s)
        self.assertNotIn(9, skip_s)
        self.assertEqual(skip_b, set())

        # Only `else` arm ran -> exact 1/2 = 50% branch coverage!
        regs = [
            _reg(1, 5), _reg(2, 5), _reg(4, 5),
            _reg(5, 0), _reg(9, 5),
            _reg(13, 5), _reg(14, 5), _reg(18, 0),
            _reg(21, 5), _reg(23, 5), _reg(24, 5), _reg(28, 0), _reg(31, 5),
        ]
        hits, n_arms = cov.extract_branch_hits(regs, skip_s, skip_b)
        self.assertEqual(n_arms, 2)
        self.assertEqual(hits, [0, 1])

    def test_io_bind_error_exits_stripped_but_author_throw_kept(self):
        c_lines = """
LEAN_EXPORT lean_object* lp_p_ioFn(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_;
v___x_2_ = lp_p_step1(v_x_1_);
if (lean_obj_tag(v___x_2_) == 0)
{
lean_object* v_a_3_; lean_object* v___x_4_;
v_a_3_ = lean_ctor_get(v___x_2_, 0);
lean_dec_ref(v___x_2_);
v___x_4_ = lp_p_step2(v_a_3_);
if (lean_obj_tag(v___x_4_) == 0)
{
lean_object* v_a_5_;
v_a_5_ = lean_ctor_get(v___x_4_, 0);
return v___x_4_;
}
else
{
lean_object* v_a_6_; lean_object* v___x_7_;
v_a_6_ = lean_ctor_get(v___x_4_, 0);
v___x_7_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7_, 0, v_a_6_);
return v___x_7_;
}
}
else
{
lean_dec_ref(v_x_1_);
return v___x_2_;
}
}
}
LEAN_EXPORT lean_object* lp_p_ioFn___boxed(lean_object* v_x_1_, lean_object* v_w_2_){
_start:
{
return lp_p_ioFn(v_x_1_);
}
}
""".strip().splitlines()
        skip_s, skip_b = cov.analyze_c_lines(c_lines)
        # Both `else` arms (L19 rewrap tag 1, L28 direct return) are IO bind error exits
        self.assertEqual(skip_b, {19, 28})
        # When both steps succeed, coverage is 2/2 = 100%
        regs = [_reg(1, 3), _reg(2, 3), _reg(6, 3), _reg(7, 3), _reg(12, 3), _reg(13, 3), _reg(19, 0), _reg(28, 0)]
        hits, n_arms = cov.extract_branch_hits(regs, skip_s, skip_b)
        self.assertEqual((hits, n_arms), ([1, 1], 2))

    def test_author_throw_closed_const_never_stripped(self):
        c_lines = """
LEAN_EXPORT lean_object* lp_p_ioThrow(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_;
v___x_2_ = lp_p_ofHex(v_x_1_);
if (lean_obj_tag(v___x_2_) == 0)
{
lean_object* v___x_3_;
v___x_3_ = ((lean_object*)(lp_p_ioThrow___closed__0));
return v___x_3_;
}
else
{
lean_object* v_val_4_; lean_object* v___x_5_;
v_val_4_ = lean_ctor_get(v___x_2_, 0);
v___x_5_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5_, 0, v_val_4_);
return v___x_5_;
}
}
}
LEAN_EXPORT lean_object* lp_p_ioThrow___boxed(lean_object* v_x_1_, lean_object* v_w_2_){
_start:
{
return lp_p_ioThrow(v_x_1_);
}
}
""".strip().splitlines()
        _, skip_b = cov.analyze_c_lines(c_lines)
        # Neither `___closed__0` throw (L7) nor `v_val_4_` Option.some (L13) is stripped!
        self.assertEqual(skip_b, set())

    def test_except_bind_stripped_but_map_error_and_option_alt_kept(self):
        # 1. ExceptT bind (tag 0 rewraps v_a into two layers of tag 0) -> stripped
        c_except = """
LEAN_EXPORT lean_object* lp_p_rmFn(lean_object* v_x_1_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v_a_2_; lean_object* v_e_3_; lean_object* v_r_4_;
v_a_2_ = lean_ctor_get(v_x_1_, 0);
v_e_3_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_e_3_, 0, v_a_2_);
v_r_4_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_r_4_, 0, v_e_3_);
return v_r_4_;
}
else
{
return lp_p_next(v_x_1_);
}
}
}
""".strip().splitlines()
        _, skip_b = cov.analyze_c_lines(c_except)
        self.assertEqual(skip_b, {5})

        # 2. Pure Option `<|>` (`else` returns `v_x_1_` directly; `then` does NOT treat `v_x_1_` as heap) -> KEPT
        c_opt = """
LEAN_EXPORT lean_object* lp_p_alt(lean_object* v_a_1_, lean_object* v_b_2_){
_start:
{
lean_object* v___x_3_;
v___x_3_ = lp_p_tryA(v_a_1_);
if (lean_obj_tag(v___x_3_) == 0)
{
return lp_p_tryB(v_b_2_);
}
else
{
lean_dec_ref(v_b_2_);
return v___x_3_;
}
}
}
""".strip().splitlines()
        _, skip_b = cov.analyze_c_lines(c_opt)
        self.assertEqual(skip_b, set())

        # 3. Pure Except.mapError (arity(boxed) == arity -> NOT IO, so tag 1 `else` is Except.ok -> KEPT)
        c_maperr = """
LEAN_EXPORT lean_object* lp_p_mapErr(lean_object* v_x_1_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v_a_2_; lean_object* v_s_3_; lean_object* v_r_4_;
v_a_2_ = lean_ctor_get(v_x_1_, 0);
v_s_3_ = lp_p_errName(v_a_2_);
v_r_4_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_r_4_, 0, v_s_3_);
return v_r_4_;
}
else
{
lean_object* v_a_5_; lean_object* v_r_6_;
v_a_5_ = lean_ctor_get(v_x_1_, 0);
v_r_6_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_r_6_, 0, v_a_5_);
return v_r_6_;
}
}
}
LEAN_EXPORT lean_object* lp_p_mapErr___boxed(lean_object* v_x_1_){
_start:
{
return lp_p_mapErr(v_x_1_);
}
}
""".strip().splitlines()
        _, skip_b = cov.analyze_c_lines(c_maperr)
        self.assertEqual(skip_b, set())


class TestAggregation(unittest.TestCase):
    def setUp(self):
        self.decls = {
            'WinnowApp.Real.syncOnce': ('LeanApp/WinnowApp/Real/Stack.lean', 427),
            'Winnow.IO.TxBroadcaster.retractAnnouncement': ('Lean/Winnow/IO/Broadcast.lean', 389),
            'Winnow.Tx.helper': ('Lean/Winnow/Tx/Helper.lean', 10),
        }

    def test_owner_combinator_vs_stdlib_internals(self):
        # Loop body specialization -> owned by syncOnce
        self.assertEqual(
            cov.owner(['_private', 'Init', 'Data', 'Array', 'Basic', '#0', 'Array', "forIn'Unsafe", 'loop',
                       '_at_', 'WinnowApp', 'Real', 'syncOnce', 'spec_4'], self.decls),
            'WinnowApp.Real.syncOnce',
        )
        # Shared Std.DHashMap.erase specialization -> library code (None), NOT retractAnnouncement
        self.assertIsNone(
            cov.owner(['Std', 'DHashMap', 'Internal', 'Raw₀', 'erase',
                       '_at_', 'Winnow', 'IO', 'TxBroadcaster', 'retractAnnouncement', 'spec_0'], self.decls),
        )
        # Nested AssocList.foldlM inside Raw₀.expand inside syncOnce -> library code (None)
        self.assertIsNone(
            cov.owner(['Std', 'DHashMap', 'Internal', 'AssocList', 'foldlM',
                       '_at_', '_private', 'Std', 'Data', 'DHashMap', 'Internal', 'Defs', '#0',
                       'Std', 'DHashMap', 'Internal', 'Raw₀', 'expand', 'go',
                       '_at_', 'WinnowApp', 'Real', 'syncOnce', 'spec_1', 'spec_2'], self.decls),
        )

    def test_clone_merging_trampolines_and_closed_inits(self):
        fake_c = lambda _src: (set(), set())
        parts_map = {
            'lp_app_syncOnce_loop': [
                '_private', 'Init', 'Data', 'Array', 'Basic', '#0', 'Array', "forIn'Unsafe", 'loop',
                '_at_', 'WinnowApp', 'Real', 'syncOnce', 'spec_4',
            ],
            'lp_app_syncOnce_loop_clone': [
                '_private', 'Init', 'Data', 'Array', 'Basic', '#0', 'Array', "forIn'Unsafe", 'loop',
                '_at_',
                '_private', 'Init', 'Data', 'Array', 'Basic', '#0', 'Array', "forIn'Unsafe", 'loop',
                '_at_', 'WinnowApp', 'Real', 'syncOnce', 'spec_4', 'spec_5',
            ],
            'lp_app_helper': ['Winnow', 'Tx', 'helper'],
            'lp_app_helper___redArg': ['Winnow', 'Tx', 'helper', '_redArg'],
            'lp_app_helper___closed__0': ['Winnow', 'Tx', 'helper', '_closed_0'],
            'lp_app_retract': ['Winnow', 'IO', 'TxBroadcaster', 'retractAnnouncement'],
            'lp_app_dhashmap_erase': [
                'Std', 'DHashMap', 'Internal', 'Raw₀', 'erase',
                '_at_', 'Winnow', 'IO', 'TxBroadcaster', 'retractAnnouncement', 'spec_0',
            ],
        }
        export_fns = [
            # Iter-1 loop copy: branches [1, 0, 1]
            {'name': 'lp_app_syncOnce_loop', 'filenames': ['a.c'],
             'regions': [_reg(1, 5), _reg(2, 5), _reg(3, 0), _reg(4, 2)]},
            # Iter-2+ self-clone: branches [0, 1, 0] -> OR-merged should be 3/3!
            {'name': 'lp_app_syncOnce_loop_clone', 'filenames': ['a.c'],
             'regions': [_reg(10, 3), _reg(11, 0), _reg(12, 3), _reg(13, 0)]},
            # Full-arity 0-branch trampoline (0 hits) + ___redArg (1/1 hit) -> trampoline skipped!
            {'name': 'lp_app_helper', 'filenames': ['a.c'], 'regions': [_reg(20, 0)]},
            {'name': 'lp_app_helper___redArg', 'filenames': ['a.c'], 'regions': [_reg(30, 9)]},
            # Static closed constant initializer -> skipped!
            {'name': '_init_lp_app_helper___closed__0', 'filenames': ['a.c'], 'regions': [_reg(40, 1)]},
            # Uncalled retractAnnouncement (0/2) + shared DHashMap.erase (2/2) -> retract stays 0/2!
            {'name': 'lp_app_retract', 'filenames': ['a.c'], 'regions': [_reg(50, 0), _reg(51, 0), _reg(52, 0)]},
            {'name': 'lp_app_dhashmap_erase', 'filenames': ['a.c'], 'regions': [_reg(60, 10), _reg(61, 5), _reg(62, 5)]},
        ]
        per, lib_br, unattr_br = cov.aggregate_functions(export_fns, parts_map, self.decls, c_analyzer=fake_c)
        self.assertEqual(per['WinnowApp.Real.syncOnce'], {'branches': 3, 'covered': 3, 'c_functions': 1})
        self.assertEqual(per['Winnow.Tx.helper'], {'branches': 1, 'covered': 1, 'c_functions': 1})
        self.assertEqual(per['Winnow.IO.TxBroadcaster.retractAnnouncement'], {'branches': 2, 'covered': 0, 'c_functions': 1})
        self.assertEqual(lib_br, 2)
        self.assertEqual(unattr_br, 0)

    def test_crap_score(self):
        self.assertAlmostEqual(cov.crap_score(30, 1.0), 30.0)
        self.assertAlmostEqual(cov.crap_score(10, 0.0), 110.0)
        self.assertAlmostEqual(cov.crap_score(10, 0.5), 100 * 0.125 + 10)

    def test_c_references_reads_column0_statements_and_skips_prototypes(self):
        c_lines = """
LEAN_EXPORT lean_object* lp_winnow_protoOnly(lean_object*);
static lean_object* lp_winnow_globalProto;
static const lean_closure_object lp_winnow_hmac___closed__0_value = {.m_header = {}, .m_fun = (void*)lp_winnow_sha256, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
LEAN_EXPORT lean_object* lp_winnow_caller(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_;
v___x_2_ = lp_winnow_callee(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_winnow_afterProto(lean_object*);
""".strip().splitlines()
        refs = list(cov.c_references_lines(c_lines))
        self.assertEqual(refs, [
            ('lp_winnow_hmac___closed__0', {'lp_winnow_sha256'}),
            ('lp_winnow_caller', {'lp_winnow_callee'}),
        ])


if __name__ == '__main__':
    unittest.main()
