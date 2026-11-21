import Maize.Core

-- The DWDS instance (Potvin 2023, §5.3.9, §5.5.3) and the thesis's container example.

namespace Maize.DWDS

/-! ## States, modes, hit -/

inductive State where
  | no        -- 00
  | yes       -- 01
  | yesAndNo  -- 10
  | yesOrNo   -- 11
  deriving DecidableEq, Repr

inductive Mode where
  | not     -- 00, no assertion
  | must    -- 01
  | may     -- 10
  | should  -- 11
  deriving DecidableEq, Repr

-- everything hits except `yes` against `no` (§5.5.3)
-- PROVISIONAL: `yesAndNo` against `yesOrNo` is unstated in the thesis; here a hit
def hit : State → State → Prop
  | .yes, .no => False
  | .no, .yes => False
  | _, _ => True

instance : DecidableRel hit := fun e o => by
  cases e <;> cases o <;> simp only [hit] <;> infer_instance

abbrev dwds : Logic := ⟨State, Mode, hit, .not⟩

instance {C A : Type} [Fintype C] (k : Clause dwds C A) (i : Is dwds C) :
    Decidable (k.Invoked i) :=
  Fintype.decidableForallFintype

/-! ## The hit relation -/

theorem hit_refl (s : State) : hit s s := by
  cases s <;> trivial

theorem hit_symm {e o : State} : hit e o → hit o e := by
  cases e <;> cases o <;> simp [hit]

-- `yes` hits `yesOrNo`, `yesOrNo` hits `no`, but `yes` misses `no`
theorem hit_not_trans : ¬ ∀ x y z : State, hit x y → hit y z → hit x z :=
  fun h => h .yes .yesOrNo .no trivial trivial

/-! ## Precision -/

-- every state is at least as precise as `yesOrNo`
theorem refines_yesOrNo (o : State) : dwds.Refines o .yesOrNo := by
  intro e _
  cases e <;> trivial

-- every state is at least as precise as `yesAndNo`
theorem refines_yesAndNo (o : State) : dwds.Refines o .yesAndNo := by
  intro e _
  cases e <;> trivial

-- `yes` and `no` are incomparable
theorem yes_not_refines_no : ¬ dwds.Refines .yes .no :=
  fun h => h .yes trivial

/-! ## Conservative extension over ordinary decision tables -/

-- ordinary decision tables: states are `Bool`, hit is equality
abbrev ordinary : Logic := ⟨Bool, Mode, (· = ·), .not⟩

-- `true ↦ yes`, `false ↦ no`
def ofBool : Bool → State
  | true => .yes
  | false => .no

-- an ordinary clause read as a DWDS clause
def _root_.Maize.Clause.toDWDS {C A : Type} (k : Clause ordinary C A) : Clause dwds C A :=
  ⟨ofBool ∘ k.expects, k.asserts⟩

-- an ordinary table read as a DWDS table
def _root_.Maize.Table.toDWDS {C A : Type} (t : Table ordinary C A) : Table dwds C A :=
  ⟨t.clauses.map Clause.toDWDS⟩

-- on `yes` and `no`, hit is equality
theorem hit_ofBool (x y : Bool) : hit (ofBool x) (ofBool y) ↔ x = y := by
  sorry

theorem invoked_toDWDS {C A : Type} (k : Clause ordinary C A) (b : Is ordinary C) :
    k.toDWDS.Invoked (ofBool ∘ b) ↔ k.Invoked b := by
  sorry

-- with only `yes` and `no`, a DWDS table means what the ordinary table means
theorem ought_toDWDS {C A : Type} (t : Table ordinary C A) (b : Is ordinary C)
    (a : A) (m : Mode) :
    t.toDWDS.Ought (ofBool ∘ b) a m ↔ t.Ought b a m := by
  sorry

/-! ## Container example (Figure 28, Figures 30–31) -/

inductive Cond where
  | loaded | inspected | locked
  deriving DecidableEq, Fintype

inductive Asrt where
  | green | yellow | red | stevedore | insurance
  deriving DecidableEq

-- a column, written in Figure 28's row order: expected states, then modes
def scenario (eLoaded eInspected eLocked : State)
    (mGreen mYellow mRed mStevedore mInsurance : Mode) : Clause dwds Cond Asrt where
  expects
    | .loaded => eLoaded
    | .inspected => eInspected
    | .locked => eLocked
  asserts
    | .green => mGreen
    | .yellow => mYellow
    | .red => mRed
    | .stevedore => mStevedore
    | .insurance => mInsurance

def container : Table dwds Cond Asrt := ⟨[
  --        loaded    inspected  locked      green  yellow  red    stevedore insurance
  scenario .no       .no        .yesOrNo    .must  .not    .not   .should   .not,     -- A
  scenario .yesOrNo  .yesOrNo   .yes        .must  .not    .not   .may      .must,    -- B
  scenario .no       .yesOrNo   .no         .not   .must   .not   .should   .must,    -- C
  scenario .yes      .no        .yes        .not   .not    .must  .must     .may,     -- D
  scenario .yes      .yes       .no         .not   .must   .not   .must     .must,    -- E
  scenario .yes      .no        .no         .not   .must   .not   .must     .not,     -- F
  scenario .no       .yes       .yes        .must  .not    .not   .not      .not,     -- G
  scenario .yesAndNo .yes       .yes        .must  .not    .not   .may      .must     -- H
]⟩

-- observed states of the three conditions
def observe (oLoaded oInspected oLocked : State) : Is dwds Cond
  | .loaded => oLoaded
  | .inspected => oInspected
  | .locked => oLocked

-- Figure 30: not loaded, inspected, not locked → only scenario C
def isA : Is dwds Cond := observe .no .yes .no

theorem exampleA :
    container.execute isA .green = [] ∧
    container.execute isA .yellow = [.must] ∧
    container.execute isA .red = [] ∧
    container.execute isA .stevedore = [.should] ∧
    container.execute isA .insurance = [.must] := by
  decide

-- Figure 31: loaded, not inspected, locked → scenarios B and D
def isB : Is dwds Cond := observe .yes .no .yes

theorem exampleB :
    container.execute isB .green = [.must] ∧
    container.execute isB .yellow = [] ∧
    container.execute isB .red = [.must] ∧
    container.execute isB .stevedore = [.may, .must] ∧
    container.execute isB .insurance = [.must, .may] := by
  decide

-- in example B the stevedore notification is left to a human
theorem exampleB_stevedore_deferred : container.Deferred isB .stevedore :=
  ⟨.may, .must,
    (container.mem_execute isB .stevedore .may).mp (by decide),
    (container.mem_execute isB .stevedore .must).mp (by decide),
    by decide⟩

end Maize.DWDS
import Maize.Core

-- The DWDS instance (Potvin 2023, §5.3.9, §5.5.3) and the thesis's container example.

namespace Maize.DWDS

/-! ## States, modes, hit -/

inductive State where
  | no        -- 00
  | yes       -- 01
  | yesAndNo  -- 10
  | yesOrNo   -- 11
  deriving DecidableEq, Repr

inductive Mode where
  | not     -- 00, no assertion
  | must    -- 01
  | may     -- 10
  | should  -- 11
  deriving DecidableEq, Repr

-- everything hits except `yes` against `no` (§5.5.3)
-- PROVISIONAL: `yesAndNo` against `yesOrNo` is unstated in the thesis; here a hit
def hit : State → State → Prop
  | .yes, .no => False
  | .no, .yes => False
  | _, _ => True

instance : DecidableRel hit := fun e o => by
  cases e <;> cases o <;> simp only [hit] <;> infer_instance

abbrev dwds : Logic := ⟨State, Mode, hit, .not⟩

instance {C A : Type} [Fintype C] (k : Clause dwds C A) (i : Is dwds C) :
    Decidable (k.Invoked i) :=
  Fintype.decidableForallFintype

/-! ## The hit relation -/

theorem hit_refl (s : State) : hit s s := by
  cases s <;> trivial

theorem hit_symm {e o : State} : hit e o → hit o e := by
  cases e <;> cases o <;> simp [hit]

-- `yes` hits `yesOrNo`, `yesOrNo` hits `no`, but `yes` misses `no`
theorem hit_not_trans : ¬ ∀ x y z : State, hit x y → hit y z → hit x z :=
  fun h => h .yes .yesOrNo .no trivial trivial

/-! ## Precision -/

-- every state is at least as precise as `yesOrNo`
theorem refines_yesOrNo (o : State) : dwds.Refines o .yesOrNo := by
  intro e _
  cases e <;> trivial

-- every state is at least as precise as `yesAndNo`
theorem refines_yesAndNo (o : State) : dwds.Refines o .yesAndNo := by
  intro e _
  cases e <;> trivial

-- `yes` and `no` are incomparable
theorem yes_not_refines_no : ¬ dwds.Refines .yes .no :=
  fun h => h .yes trivial

/-! ## Conservative extension over ordinary decision tables -/

-- ordinary decision tables: states are `Bool`, hit is equality
abbrev ordinary : Logic := ⟨Bool, Mode, (· = ·), .not⟩

-- `true ↦ yes`, `false ↦ no`
def ofBool : Bool → State
  | true => .yes
  | false => .no

-- an ordinary clause read as a DWDS clause
def _root_.Maize.Clause.toDWDS {C A : Type} (k : Clause ordinary C A) : Clause dwds C A :=
  ⟨ofBool ∘ k.expects, k.asserts⟩

-- an ordinary table read as a DWDS table
def _root_.Maize.Table.toDWDS {C A : Type} (t : Table ordinary C A) : Table dwds C A :=
  ⟨t.clauses.map Clause.toDWDS⟩

-- on `yes` and `no`, hit is equality
theorem hit_ofBool (x y : Bool) : hit (ofBool x) (ofBool y) ↔ x = y := by
  sorry

theorem invoked_toDWDS {C A : Type} (k : Clause ordinary C A) (b : Is ordinary C) :
    k.toDWDS.Invoked (ofBool ∘ b) ↔ k.Invoked b := by
  sorry

-- with only `yes` and `no`, a DWDS table means what the ordinary table means
theorem ought_toDWDS {C A : Type} (t : Table ordinary C A) (b : Is ordinary C)
    (a : A) (m : Mode) :
    t.toDWDS.Ought (ofBool ∘ b) a m ↔ t.Ought b a m := by
  sorry

/-! ## Container example (Figure 28, Figures 30–31) -/

inductive Cond where
  | loaded | inspected | locked
  deriving DecidableEq, Fintype

inductive Asrt where
  | green | yellow | red | stevedore | insurance
  deriving DecidableEq

-- a column, written in Figure 28's row order: expected states, then modes
def scenario (eLoaded eInspected eLocked : State)
    (mGreen mYellow mRed mStevedore mInsurance : Mode) : Clause dwds Cond Asrt where
  expects
    | .loaded => eLoaded
    | .inspected => eInspected
    | .locked => eLocked
  asserts
    | .green => mGreen
    | .yellow => mYellow
    | .red => mRed
    | .stevedore => mStevedore
    | .insurance => mInsurance

def container : Table dwds Cond Asrt := ⟨[
  --        loaded    inspected  locked      green  yellow  red    stevedore insurance
  scenario .no       .no        .yesOrNo    .must  .not    .not   .should   .not,     -- A
  scenario .yesOrNo  .yesOrNo   .yes        .must  .not    .not   .may      .must,    -- B
  scenario .no       .yesOrNo   .no         .not   .must   .not   .should   .must,    -- C
  scenario .yes      .no        .yes        .not   .not    .must  .must     .may,     -- D
  scenario .yes      .yes       .no         .not   .must   .not   .must     .must,    -- E
  scenario .yes      .no        .no         .not   .must   .not   .must     .not,     -- F
  scenario .no       .yes       .yes        .must  .not    .not   .not      .not,     -- G
  scenario .yesAndNo .yes       .yes        .must  .not    .not   .may      .must     -- H
]⟩

-- observed states of the three conditions
def observe (oLoaded oInspected oLocked : State) : Is dwds Cond
  | .loaded => oLoaded
  | .inspected => oInspected
  | .locked => oLocked

-- Figure 30: not loaded, inspected, not locked → only scenario C
def isA : Is dwds Cond := observe .no .yes .no

theorem exampleA :
    container.execute isA .green = [] ∧
    container.execute isA .yellow = [.must] ∧
    container.execute isA .red = [] ∧
    container.execute isA .stevedore = [.should] ∧
    container.execute isA .insurance = [.must] := by
  decide

-- Figure 31: loaded, not inspected, locked → scenarios B and D
def isB : Is dwds Cond := observe .yes .no .yes

theorem exampleB :
    container.execute isB .green = [.must] ∧
    container.execute isB .yellow = [] ∧
    container.execute isB .red = [.must] ∧
    container.execute isB .stevedore = [.may, .must] ∧
    container.execute isB .insurance = [.must, .may] := by
  decide

-- in example B the stevedore notification is left to a human
theorem exampleB_stevedore_deferred : container.Deferred isB .stevedore :=
  ⟨.may, .must,
    (container.mem_execute isB .stevedore .may).mp (by decide),
    (container.mem_execute isB .stevedore .must).mp (by decide),
    by decide⟩

end Maize.DWDS
