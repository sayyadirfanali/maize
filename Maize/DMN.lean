import Maize.Core

-- DMN decision tables (OMG DMN, S-FEEL unary tests) as a Maize logic

namespace Maize.DMN

/-! ## Values and tests -/

inductive Value where
  | int (n : Int)
  | str (s : String)
  | bool (b : Bool)
  deriving DecidableEq, Repr

-- S-FEEL unary tests, without `not(…)` and lists of tests
inductive Test where
  | any                                             -- `-`
  | eq (v : Value)                                  -- `v`
  | lt (n : Int)                                    -- `< n`
  | le (n : Int)                                    -- `<= n`
  | gt (n : Int)                                    -- `> n`
  | ge (n : Int)                                    -- `>= n`
  | range (lo hi : Int) (loClosed hiClosed : Bool)  -- `[lo..hi]`, `(lo..hi]`, …
  | oneOf (vs : List Value)                         -- `v₁, v₂, …`
  deriving Repr

-- `w` passes test `t`; comparisons and ranges pass integers only
def passes : Test → Value → Prop
  | .any, _ => True
  | .eq v, w => w = v
  | .lt n, .int m => m < n
  | .le n, .int m => m ≤ n
  | .gt n, .int m => m > n
  | .ge n, .int m => m ≥ n
  | .range lo hi true true, .int m => lo ≤ m ∧ m ≤ hi
  | .range lo hi true false, .int m => lo ≤ m ∧ m < hi
  | .range lo hi false true, .int m => lo < m ∧ m ≤ hi
  | .range lo hi false false, .int m => lo < m ∧ m < hi
  | .oneOf vs, w => w ∈ vs
  | _, _ => False

/-! ## Shapes: what a test passes -/

-- `m` is at least the lower bound `lo`, if there is one
def Above (lo : Option Int) (m : Int) : Prop :=
  match lo with
  | none => True
  | some l => l ≤ m

-- `m` is at most the upper bound `hi`, if there is one
def Below (hi : Option Int) (m : Int) : Prop :=
  match hi with
  | none => True
  | some h => m ≤ h

instance : (lo : Option Int) → (m : Int) → Decidable (Above lo m)
  | none, _ => isTrue trivial
  | some l, m => inferInstanceAs (Decidable (l ≤ m))

instance : (hi : Option Int) → (m : Int) → Decidable (Below hi m)
  | none, _ => isTrue trivial
  | some h, m => inferInstanceAs (Decidable (m ≤ h))

-- every test passes all values, the integers in a closed interval, or a list of values
inductive Shape where
  | all
  | ints (lo hi : Option Int)  -- `none` is unbounded
  | vals (vs : List Value)

def Shape.Mem : Shape → Value → Prop
  | .all, _ => True
  | .ints lo hi, .int m => Above lo m ∧ Below hi m
  | .ints _ _, _ => False
  | .vals vs, w => w ∈ vs

-- `Shape.Mem` as a computation
def Shape.memB : Shape → Value → Bool
  | .all, _ => true
  | .ints lo hi, .int m => decide (Above lo m) && decide (Below hi m)
  | .ints _ _, _ => false
  | .vals vs, w => decide (w ∈ vs)

theorem Shape.memB_iff (s : Shape) (w : Value) : s.memB w = true ↔ s.Mem w := by
  cases s <;> cases w <;> simp [Shape.memB, Shape.Mem]

instance (s : Shape) (w : Value) : Decidable (s.Mem w) :=
  decidable_of_iff _ (Shape.memB_iff s w)

def Test.shape : Test → Shape
  | .any => .all
  | .eq v => .vals [v]
  | .lt n => .ints none (some (n - 1))
  | .le n => .ints none (some n)
  | .gt n => .ints (some (n + 1)) none
  | .ge n => .ints (some n) none
  | .range lo hi true true => .ints (some lo) (some hi)
  | .range lo hi true false => .ints (some lo) (some (hi - 1))
  | .range lo hi false true => .ints (some (lo + 1)) (some hi)
  | .range lo hi false false => .ints (some (lo + 1)) (some (hi - 1))
  | .oneOf vs => .vals vs

theorem passes_iff_mem (t : Test) (w : Value) : passes t w ↔ t.shape.Mem w := by
  cases t with
  | range lo hi lc hc =>
    cases w <;> cases lc <;> cases hc <;>
      simp only [passes, Test.shape, Shape.Mem, Above, Below] <;> omega
  | _ =>
    cases w <;>
      simp only [passes, Test.shape, Shape.Mem, Above, Below, List.mem_singleton, true_and,
        and_true] <;> omega

instance (t : Test) (w : Value) : Decidable (passes t w) :=
  decidable_of_iff _ (passes_iff_mem t w).symm

-- outputs are values; `none` is the absent mode and never occurs in DMN rules
abbrev dmn : Logic := ⟨Test, Value, Option Value, passes, none⟩

instance {C A : Type} [Fintype C] (k : Clause dmn C A) (i : Is dmn C) :
    Decidable (k.Invoked i) :=
  Fintype.decidableForallFintype

instance {C A : Type} (a : A) (k k' : Clause dmn C A) : Decidable (k.Disagree a k') :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-! ## Overlap of two tests -/

-- the larger of two lower bounds
def maxLo : Option Int → Option Int → Option Int
  | none, b => b
  | a, none => a
  | some a, some b => some (max a b)

-- the smaller of two upper bounds
def minHi : Option Int → Option Int → Option Int
  | none, b => b
  | a, none => a
  | some a, some b => some (min a b)

theorem above_maxLo (l l' : Option Int) (m : Int) :
    Above (maxLo l l') m ↔ Above l m ∧ Above l' m := by
  cases l <;> cases l' <;> simp only [maxLo, Above, Int.max_le, true_and, and_true]

theorem below_minHi (h h' : Option Int) (m : Int) :
    Below (minHi h h') m ↔ Below h m ∧ Below h' m := by
  cases h <;> cases h' <;> simp only [minHi, Below, Int.le_min, true_and, and_true]

-- the values in both `s` and `s'`
def Shape.inter : Shape → Shape → Shape
  | .vals vs, s => .vals (vs.filter s.memB)
  | s, .vals vs => .vals (vs.filter s.memB)
  | .all, s => s
  | s, .all => s
  | .ints l h, .ints l' h' => .ints (maxLo l l') (minHi h h')

theorem Shape.mem_inter (s s' : Shape) (w : Value) :
    (s.inter s').Mem w ↔ s.Mem w ∧ s'.Mem w := by
  cases s <;> cases s' <;> cases w <;>
    simp only [Shape.inter, Shape.Mem, List.mem_filter, Shape.memB_iff, above_maxLo,
      below_minHi, true_and, and_true, false_and, and_false] <;>
    first
    | exact and_comm
    | exact and_and_and_comm

-- some value is in `s`, as a computation
def Shape.nonempty : Shape → Bool
  | .all => true
  | .ints (some l) (some h) => decide (l ≤ h)
  | .ints _ _ => true
  | .vals vs => !vs.isEmpty

theorem Shape.nonempty_iff (s : Shape) : (∃ w, s.Mem w) ↔ s.nonempty = true := by
  cases s with
  | all => exact ⟨fun _ => rfl, fun _ => ⟨.int 0, trivial⟩⟩
  | vals vs =>
    cases vs with
    | nil => simp [Shape.nonempty, Shape.Mem]
    | cons v vs => exact ⟨fun _ => rfl, fun _ => ⟨v, List.mem_cons_self ..⟩⟩
  | ints lo hi =>
    constructor
    · intro ⟨w, hw⟩
      cases w with
      | int m =>
        obtain ⟨hlo, hhi⟩ := hw
        cases lo with
        | none => cases hi <;> rfl
        | some l =>
          cases hi with
          | none => rfl
          | some h => exact decide_eq_true (Int.le_trans hlo hhi)
      | str _ => exact (hw : False).elim
      | bool _ => exact (hw : False).elim
    · intro hne
      cases lo with
      | none =>
        cases hi with
        | none => exact ⟨.int 0, trivial, trivial⟩
        | some h => exact ⟨.int h, trivial, Int.le_refl h⟩
      | some l =>
        cases hi with
        | none => exact ⟨.int l, Int.le_refl l, trivial⟩
        | some h => exact ⟨.int l, Int.le_refl l, of_decide_eq_true hne⟩

-- some value passes both `t` and `t'`
def Test.Overlap (t t' : Test) : Prop :=
  ∃ w, passes t w ∧ passes t' w

-- overlap is decided by intersecting shapes
theorem Test.overlap_iff (t t' : Test) :
    t.Overlap t' ↔ (t.shape.inter t'.shape).nonempty = true := by
  unfold Test.Overlap
  rw [← Shape.nonempty_iff]
  simp only [Shape.mem_inter, passes_iff_mem]

instance (t t' : Test) : Decidable (t.Overlap t') :=
  decidable_of_iff _ (Test.overlap_iff t t').symm

-- `a` is decisive iff every disagreeing pair has a row whose tests don't overlap
theorem decisive_iff {C A : Type} (t : Table dmn C A) (a : A) :
    t.Decisive (fun _ => True) a ↔
      ∀ k ∈ t.clauses, ∀ k' ∈ t.clauses,
        k.Disagree a k' → ∃ c, ¬ (k.expects c).Overlap (k'.expects c) :=
  Table.decisive_iff_rows (fun e e' => by simp [Test.Overlap]) t a

/-! ## Discount example -/

inductive Cond where
  | customer | size
  deriving DecidableEq

instance : Fintype Cond where
  elems := {Cond.customer, Cond.size}
  complete := by
    intro c
    cases c <;> simp

inductive Asrt where
  | discount
  deriving DecidableEq

-- a row: customer test, order-size test, discount (%)
def rule (eCustomer eSize : Test) (discount : Int) : Clause dmn Cond Asrt where
  expects
    | .customer => eCustomer
    | .size => eSize
  asserts
    | .discount => some (.int discount)

def discount : Table dmn Cond Asrt := ⟨[
  rule (.eq (.str "Business")) (.lt 10) 5,
  rule (.eq (.str "Business")) (.ge 10) 10,
  rule (.eq (.str "Private"))  .any     0
]⟩

-- observed customer and order size
def observe (oCustomer : String) (oSize : Int) : Is dmn Cond
  | .customer => .str oCustomer
  | .size => .int oSize

theorem discount_examples :
    discount.execute (observe "Business" 3) .discount = [some (.int 5)] ∧
    discount.execute (observe "Business" 12) .discount = [some (.int 10)] ∧
    discount.execute (observe "Private" 12) .discount = [some (.int 0)] ∧
    discount.execute (observe "Other" 12) .discount = [] := by
  decide

-- no input makes the discount ambiguous
theorem discount_decisive : discount.Decisive (fun _ => True) .discount := by
  rw [decisive_iff]
  decide

-- a catch-all meant as "otherwise, no discount"
def withDefault : Table dmn Cond Asrt :=
  discount.append ⟨[rule .any .any 0]⟩

-- it fires next to the business rules, so the discount becomes ambiguous
theorem withDefault_not_decisive : ¬ withDefault.Decisive (fun _ => True) .discount := by
  rw [decisive_iff]
  decide

end Maize.DMN
