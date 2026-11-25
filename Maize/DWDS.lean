import Maize.Core

-- The DWDS instance (Potvin 2023, §5.3.9, §5.5.3) and the thesis's container example.

namespace Maize.DWDS

/-! ## Logic -/

-- what a cell of a scenario expects of an input condition
inductive Cell where
  | no        -- 00
  | yes       -- 01
  | yesAndNo  -- 10
  | yesOrNo   -- 11
  deriving DecidableEq, Repr

instance : Fintype Cell where
  elems := {Cell.no, Cell.yes, Cell.yesAndNo, Cell.yesOrNo}
  complete := by
    intro s
    cases s <;> simp

-- what a fact says
inductive Fact where
  | no
  | yes
  deriving DecidableEq, Repr

instance : Fintype Fact where
  elems := {Fact.no, Fact.yes}
  complete := by
    intro f
    cases f <;> simp

inductive Mode where
  | not     -- 00, no assertion
  | must    -- 01
  | may     -- 10
  | should  -- 11
  deriving DecidableEq, Repr

-- a cell against a fact, as in §5.5.3:
-- YES and NO need the same fact, YES-AND-NO and YES-OR-NO accept either
def hit : Cell → Fact → Prop
  | .yes, .yes => True
  | .no, .no => True
  | .yesAndNo, _ => True
  | .yesOrNo, _ => True
  | _, _ => False

instance : DecidableRel hit := fun e o => by
  cases e <;> cases o <;> simp only [hit] <;> infer_instance

abbrev dwds : Logic := ⟨Cell, Fact, Mode, hit, .not⟩

instance {C A : Type} [Fintype C] (k : Clause dwds C A) (i : Is dwds C) :
    Decidable (k.Invoked i) :=
  Fintype.decidableForallFintype

instance {C A : Type} (a : A) (k k' : Clause dwds C A) : Decidable (k.Disagree a k') :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-! ## Compatible Cells -/

-- two cells some fact satisfies: all but YES against NO
def Compatible : Cell → Cell → Prop
  | .yes, .no => False
  | .no, .yes => False
  | _, _ => True

instance : DecidableRel Compatible := fun e e' => by
  cases e <;> cases e' <;> simp only [Compatible] <;> infer_instance

theorem compatible_iff (e e' : Cell) :
    (∃ b, True ∧ hit e b ∧ hit e' b) ↔ Compatible e e' := by
  cases e <;> cases e' <;> decide

theorem compatible_symm {e e' : Cell} : Compatible e e' → Compatible e' e := by
  cases e <;> cases e' <;> simp [Compatible]

-- `yes` with `yesOrNo`, `yesOrNo` with `no`, but not `yes` with `no`
theorem compatible_not_trans :
    ¬ ∀ x y z : Cell, Compatible x y → Compatible y z → Compatible x z :=
  fun h => h .yes .yesOrNo .no trivial trivial

/-! ## Conservative Extension -/

-- ordinary decision tables: Boolean cells, hit is equality
abbrev ordinary : Logic := ⟨Bool, Bool, Mode, (· = ·), .not⟩

-- `true` is YES, `false` is NO
def ofBool : Bool → Cell
  | true => .yes
  | false => .no

def factOfBool : Bool → Fact
  | true => .yes
  | false => .no

-- `t` read as a DWDS table
def _root_.Maize.Table.toDWDS {C A : Type} (t : Table ordinary C A) : Table dwds C A :=
  Table.map (L := ordinary) (L' := dwds) ofBool id t

theorem hit_ofBool (x y : Bool) : hit (ofBool x) (factOfBool y) ↔ x = y := by
  cases x <;> cases y <;> decide

-- the DWDS reading gives the same results as the ordinary one
theorem ought_toDWDS {C A : Type} (t : Table ordinary C A) (b : Is ordinary C)
    (a : A) (m : Mode) :
    t.toDWDS.Ought (factOfBool ∘ b) a m ↔ t.Ought b a m :=
  Table.ought_map (L := ordinary) (L' := dwds) (fE := ofBool) (fO := factOfBool) (g := id)
    hit_ofBool Function.injective_id (fun _ => Iff.rfl) t b a m

/-! ## Choice Points -/

-- `a` is decisive iff every disagreeing pair has a YES against NO in some row
theorem decisive_iff {C A : Type} (t : Table dwds C A) (a : A) :
    t.Decisive (fun _ => True) a ↔
      ∀ k ∈ t.clauses, ∀ k' ∈ t.clauses,
        k.Disagree a k' → ∃ c, ¬ Compatible (k.expects c) (k'.expects c) :=
  Table.decisive_iff_rows (P := fun _ => True) compatible_iff t a

-- a fact both cells accept, YES if possible, otherwise NO (like DMN's `Shape.sample`)
def sample (e e' : Cell) : Option Fact :=
  if hit e .yes ∧ hit e' .yes then some .yes
  else if hit e .no ∧ hit e' .no then some .no
  else none

theorem sample_sound :
    ∀ e e' b, sample e e' = some b → True ∧ hit e b ∧ hit e' b := by
  decide

theorem sample_complete :
    ∀ e e', (∃ b, True ∧ hit e b ∧ hit e' b) → (sample e e').isSome := by
  decide

def sampler : dwds.Sampler (fun _ => True) where
  sample := DWDS.sample
  sound h := sample_sound _ _ _ h
  complete h := sample_complete _ _ h

/-! ## Catch-All Cells -/

theorem universal_yesOrNo : dwds.Universal .yesOrNo := by
  intro o
  cases o <;> trivial

theorem universal_yesAndNo : dwds.Universal .yesAndNo := by
  intro o
  cases o <;> trivial

/-! ## Example: Container (from Potvin 2023) -/

inductive Cond where
  | loaded
  | inspected
  | locked
  deriving DecidableEq

instance : Fintype Cond where
  elems := {Cond.loaded, Cond.inspected, Cond.locked}
  complete := by
    intro c
    cases c <;> simp

inductive Asrt where
  | green
  | yellow
  | red
  | stevedore
  | insurance
  deriving DecidableEq, Repr

instance : Fintype Asrt where
  elems := {Asrt.green, Asrt.yellow, Asrt.red, Asrt.stevedore, Asrt.insurance}
  complete := by
    intro a
    cases a <;> simp

-- all assertions, in Figure 28's row order
def allAsrt : List Asrt := [.green, .yellow, .red, .stevedore, .insurance]

-- a column, written in Figure 28's row order: cells, then modes
def scenario (eLoaded eInspected eLocked : Cell)
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

-- facts for the three conditions
def observe (oLoaded oInspected oLocked : Fact) : Is dwds Cond
  | .loaded => oLoaded
  | .inspected => oInspected
  | .locked => oLocked

-- Figure 30: not loaded, inspected, not locked → only scenario C
def isA : Is dwds Cond := observe .no .yes .no

theorem exampleA :
    container.activeOutcomes isA allAsrt =
      [[(.yellow, .must), (.stevedore, .should), (.insurance, .must)]] := by
  decide

theorem exampleA_no_choice : ¬ container.Choice isA := by
  rw [Table.choice_iff]
  decide

-- Figure 31: loaded, not inspected, locked → scenarios B and D, kept apart
def isB : Is dwds Cond := observe .yes .no .yes

theorem exampleB :
    container.activeOutcomes isB allAsrt =
      [[(.green, .must), (.stevedore, .may), (.insurance, .must)],    -- B
       [(.red, .must), (.stevedore, .must), (.insurance, .may)]] := by  -- D
  decide

theorem exampleB_choice : container.Choice isB := by
  rw [Table.choice_iff]
  decide

-- in example B the stevedore notification gets two modes
theorem exampleB_stevedore_deferred : container.Deferred isB .stevedore :=
  ⟨.may, .must,
    (container.ought_iff_outcomes isB .stevedore .may).mpr (by decide),
    (container.ought_iff_outcomes isB .stevedore .must).mpr (by decide),
    by decide⟩

-- not loaded, not inspected, locked → scenarios A and B
def isAB : Is dwds Cond := observe .no .no .yes

theorem exampleAB :
    container.activeOutcomes isAB allAsrt =
      [[(.green, .must), (.stevedore, .should)],                       -- A
       [(.green, .must), (.stevedore, .may), (.insurance, .must)]] := by  -- B
  decide

theorem exampleAB_choice : container.Choice isAB := by
  rw [Table.choice_iff]
  decide

/-! ## Finding Choice Points -/

-- the first choice: A against B, with insurance only in B, at the facts of `isAB`
theorem container_choice :
    (container.findChoice sampler).map
      (fun r => (r.1.asserts .insurance, r.2.1.asserts .insurance,
        r.2.2 .loaded, r.2.2 .inspected, r.2.2 .locked)) =
    some (.not, .must, .no, .no, .yes) := by
  decide

-- stevedore: scenarios A (SHOULD) and B (MAY), at the facts of `isAB`
theorem container_stevedore_conflict :
    (container.findConflict sampler .stevedore).map
      (fun r => (r.1.asserts .stevedore, r.2.1.asserts .stevedore,
        r.2.2 .loaded, r.2.2 .inspected, r.2.2 .locked)) =
    some (.should, .may, .no, .no, .yes) := by
  decide

-- insurance: scenarios B (MUST) and D (MAY), at the facts of Figure 31
theorem container_insurance_conflict :
    (container.findConflict sampler .insurance).map
      (fun r => (r.1.asserts .insurance, r.2.1.asserts .insurance,
        r.2.2 .loaded, r.2.2 .inspected, r.2.2 .locked)) =
    some (.must, .may, .yes, .no, .yes) := by
  decide

/-! ## Catch-All Example -/

-- a catch-all meant as "otherwise, yellow light"
def withDefault : Table dwds Cond Asrt :=
  container.append ⟨[scenario .yesOrNo .yesOrNo .yesOrNo .not .must .not .not .not]⟩

-- it is not an else: in example B it applies next to B and D
theorem exampleB_withDefault :
    withDefault.activeOutcomes isB allAsrt =
      [[(.green, .must), (.stevedore, .may), (.insurance, .must)],
       [(.red, .must), (.stevedore, .must), (.insurance, .may)],
       [(.yellow, .must)]] := by
  decide

end Maize.DWDS
