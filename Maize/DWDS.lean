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

instance : Fintype State where
  elems := {State.no, State.yes, State.yesAndNo, State.yesOrNo}
  complete := by
    intro s
    cases s <;> simp

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

abbrev dwds : Logic := ⟨State, State, Mode, hit, .not⟩

instance {C A : Type} [Fintype C] (k : Clause dwds C A) (i : Is dwds C) :
    Decidable (k.Invoked i) :=
  Fintype.decidableForallFintype

instance {C A : Type} (a : A) (k k' : Clause dwds C A) : Decidable (k.Disagree a k') :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-! ## The hit relation -/

theorem hit_refl (s : State) : hit s s := by
  cases s <;> trivial

theorem hit_symm {e o : State} : hit e o → hit o e := by
  cases e <;> cases o <;> simp [hit]

-- `yes` hits `yesOrNo`, `yesOrNo` hits `no`, but `yes` misses `no`
theorem hit_not_trans : ¬ ∀ x y z : State, hit x y → hit y z → hit x z :=
  fun h => h .yes .yesOrNo .no trivial trivial

theorem hit_yesOrNo (e : State) : hit e .yesOrNo := by
  cases e <;> trivial

/-! ## Precision -/

theorem refines_yesOrNo (o : State) : dwds.Refines o .yesOrNo := by
  intro e _
  exact hit_yesOrNo e

theorem refines_yesAndNo (o : State) : dwds.Refines o .yesAndNo := by
  intro e _
  cases e <;> trivial

theorem yes_not_refines_no : ¬ dwds.Refines .yes .no :=
  fun h => h .yes trivial

/-! ## Conservative extension over ordinary decision tables -/

-- ordinary decision tables: Boolean states, hit is equality
abbrev ordinary : Logic := ⟨Bool, Bool, Mode, (· = ·), .not⟩

def ofBool : Bool → State
  | true => .yes
  | false => .no

-- `t` read as a DWDS table: `true` becomes `yes`, `false` becomes `no`
def _root_.Maize.Table.toDWDS {C A : Type} (t : Table ordinary C A) : Table dwds C A :=
  Table.map (L := ordinary) (L' := dwds) ofBool id t

theorem hit_ofBool (x y : Bool) : hit (ofBool x) (ofBool y) ↔ x = y := by
  cases x <;> cases y <;> decide

-- on Boolean facts, the DWDS reading gives the same results as the ordinary one
theorem ought_toDWDS {C A : Type} (t : Table ordinary C A) (b : Is ordinary C)
    (a : A) (m : Mode) :
    t.toDWDS.Ought (ofBool ∘ b) a m ↔ t.Ought b a m :=
  Table.ought_map (L := ordinary) (L' := dwds) (fE := ofBool) (fO := ofBool) (g := id)
    hit_ofBool Function.injective_id (fun _ => Iff.rfl) t b a m

/-! ## Choice points with definite facts -/

-- `o` is YES or NO
def Definite : State → Prop
  | .yes => True
  | .no => True
  | _ => False

instance : DecidablePred Definite := fun o => by
  cases o <;> simp only [Definite] <;> infer_instance

-- some definite `o` is hit by both `e` and `e'` iff `e` hits `e'`
theorem hit_definite_iff (e e' : State) :
    (∃ o, Definite o ∧ hit e o ∧ hit e' o) ↔ hit e e' := by
  cases e <;> cases e' <;> decide

-- with definite facts, `k` and `k'` fire together iff no row has `yes` against `no`
theorem coInvocable_definite_iff {C A : Type} (k k' : Clause dwds C A) :
    k.CoInvocable Definite k' ↔ ∀ c, hit (k.expects c) (k'.expects c) := by
  rw [Clause.coInvocable_iff]
  exact forall_congr' fun c => hit_definite_iff (k.expects c) (k'.expects c)

-- `a` is decisive iff every disagreeing pair has a `yes` against `no` in some row
theorem decisive_iff {C A : Type} (t : Table dwds C A) (a : A) :
    t.Decisive Definite a ↔
      ∀ k ∈ t.clauses, ∀ k' ∈ t.clauses,
        k.Disagree a k' → ∃ c, ¬ hit (k.expects c) (k'.expects c) :=
  Table.decisive_iff_rows hit_definite_iff t a

-- with unrestricted facts, any two clauses fire together: all `yesOrNo`
theorem coInvocable_any {C A : Type} (k k' : Clause dwds C A) :
    k.CoInvocable (fun _ => True) k' :=
  ⟨fun _ => .yesOrNo, fun _ => trivial,
    fun c => hit_yesOrNo (k.expects c), fun c => hit_yesOrNo (k'.expects c)⟩

/-! ## Catch-all states -/

theorem universal_yesOrNo : dwds.Universal .yesOrNo := by
  intro o
  cases o <;> trivial

theorem universal_yesAndNo : dwds.Universal .yesAndNo := by
  intro o
  cases o <;> trivial

/-! ## A minimal example -/

inductive MiniCond where
  | loaded | locked
  deriving DecidableEq

instance : Fintype MiniCond where
  elems := {MiniCond.loaded, MiniCond.locked}
  complete := by
    intro c
    cases c <;> simp

inductive MiniAsrt where
  | stevedore
  deriving DecidableEq

-- a scenario: expected loaded, expected locked, mode for notifying the stevedore
def miniScenario (eLoaded eLocked : State) (mStevedore : Mode) :
    Clause dwds MiniCond MiniAsrt where
  expects
    | .loaded => eLoaded
    | .locked => eLocked
  asserts
    | .stevedore => mStevedore

-- 1: loaded, locked either way → MUST notify; 2: loaded either way, locked → MAY notify
def mini : Table dwds MiniCond MiniAsrt := ⟨[
  miniScenario .yes .yesOrNo .must,
  miniScenario .yesOrNo .yes .may
]⟩

-- observed loaded and locked
def miniObserve (oLoaded oLocked : State) : Is dwds MiniCond
  | .loaded => oLoaded
  | .locked => oLocked

-- loaded and not locked: only scenario 1 applies
theorem mini_one :
    mini.execute (miniObserve .yes .no) .stevedore = [.must] := by
  decide

-- loaded and locked: both apply, so the notification is left to a human
theorem mini_both :
    mini.execute (miniObserve .yes .yes) .stevedore = [.must, .may] := by
  decide

theorem mini_deferred : mini.Deferred (miniObserve .yes .yes) .stevedore :=
  ⟨.must, .may,
    (mini.mem_execute _ .stevedore .must).mp (by decide),
    (mini.mem_execute _ .stevedore .may).mp (by decide),
    by decide⟩

/-! ## Container example (Figure 28, Figures 30–31) -/

inductive Cond where
  | loaded | inspected | locked
  deriving DecidableEq

instance : Fintype Cond where
  elems := {Cond.loaded, Cond.inspected, Cond.locked}
  complete := by
    intro c
    cases c <;> simp

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

/-! ## Choice points of the container table -/

-- with definite facts, the three lights never need a human decision
theorem container_decisive_green : container.Decisive Definite .green := by
  rw [decisive_iff]
  decide

theorem container_decisive_yellow : container.Decisive Definite .yellow := by
  rw [decisive_iff]
  decide

theorem container_decisive_red : container.Decisive Definite .red := by
  rw [decisive_iff]
  decide

-- the stevedore (A with B, B with D) and insurance (B with D) notifications
-- can need a human decision
theorem container_not_decisive_stevedore : ¬ container.Decisive Definite .stevedore := by
  rw [decisive_iff]
  decide

theorem container_not_decisive_insurance : ¬ container.Decisive Definite .insurance := by
  rw [decisive_iff]
  decide

/-! ## Finding choice points -/

-- a definite state that both `e` and `e'` hit: YES if possible, otherwise NO
def pickDefinite (e e' : State) : Option State :=
  if hit e .yes ∧ hit e' .yes then some .yes
  else if hit e .no ∧ hit e' .no then some .no
  else none

theorem pickDefinite_sound :
    ∀ e e' o, pickDefinite e e' = some o → Definite o ∧ hit e o ∧ hit e' o := by
  decide

theorem pickDefinite_complete :
    ∀ e e', (∃ o, Definite o ∧ hit e o ∧ hit e' o) → (pickDefinite e e').isSome := by
  decide

-- with definite facts, DWDS picks YES or NO condition by condition
def definiteSampler : dwds.Sampler Definite where
  sample := pickDefinite
  sound h := pickDefinite_sound _ _ _ h
  complete h := pickDefinite_complete _ _ h

-- in the minimal example, loaded and locked is where the stevedore is left to a human
theorem mini_choice :
    (mini.findConflict definiteSampler .stevedore).map
      (fun r => (r.1.asserts .stevedore, r.2.1.asserts .stevedore,
        r.2.2 .loaded, r.2.2 .locked)) =
    some (.must, .may, .yes, .yes) := by
  decide

-- stevedore: scenarios A (SHOULD) and B (MAY), when not loaded, not inspected and locked
theorem container_stevedore_choice :
    (container.findConflict definiteSampler .stevedore).map
      (fun r => (r.1.asserts .stevedore, r.2.1.asserts .stevedore,
        r.2.2 .loaded, r.2.2 .inspected, r.2.2 .locked)) =
    some (.should, .may, .no, .no, .yes) := by
  decide

-- insurance: scenarios B (MUST) and D (MAY), in the situation of Figure 31
theorem container_insurance_choice :
    (container.findConflict definiteSampler .insurance).map
      (fun r => (r.1.asserts .insurance, r.2.1.asserts .insurance,
        r.2.2 .loaded, r.2.2 .inspected, r.2.2 .locked)) =
    some (.must, .may, .yes, .no, .yes) := by
  decide

-- the lights: nothing is found, so they never need a human decision
theorem container_green_no_choice :
    (container.findConflict definiteSampler .green).isNone := by
  decide

/-! ## Findings -/

-- decisiveness is per assertion: in example B the green and red lights are both MUST
theorem exampleB_green_and_red :
    container.Determinate isB .green ∧ container.Determinate isB .red :=
  ⟨container.determinate_of_execute (m := .must) (by decide),
    container.determinate_of_execute (m := .must) (by decide)⟩

-- a catch-all meant as "otherwise, yellow light"
def withDefault : Table dwds Cond Asrt :=
  container.append ⟨[scenario .yesOrNo .yesOrNo .yesOrNo .not .must .not .not .not]⟩

-- it is not an else: in example B it fires next to B and D
theorem exampleB_withDefault :
    withDefault.execute isB .green = [.must] ∧
    withDefault.execute isB .yellow = [.must] ∧
    withDefault.execute isB .red = [.must] := by
  decide

end Maize.DWDS
