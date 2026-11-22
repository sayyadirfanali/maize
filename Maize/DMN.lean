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

/-! ## Picking results -/

-- how a decision picks its result from the matching rules (DMN calls this the hit policy)
inductive Pick where
  | unique     -- U: at most one rule may match
  | any        -- A: matching rules must have the same outputs
  | first      -- F: the first matching rule, in table order
  | collect    -- C: all matching rules, order not meaningful (no aggregation)
  | ruleOrder  -- R: all matching rules, in table order
  deriving DecidableEq, Repr

-- a DMN decision table: its rules and how to pick
structure Decision (C A : Type) where
  table : Table dmn C A
  pick : Pick

-- the result in one output column
inductive Result where
  | noMatch                          -- no rule matched: DMN's `null`
  | one (v : Option Value)           -- the result of `unique`, `any`, `first`
  | many (vs : List (Option Value))  -- the results of `collect`, `ruleOrder`
  | violation                        -- the pick's condition failed
  deriving DecidableEq, Repr

-- `k` and `k'` have the same output in every column
def SameRow {C A : Type} (k k' : Clause dmn C A) : Prop :=
  ∀ b, k.asserts b = k'.asserts b

instance {C A : Type} [Fintype A] (k k' : Clause dmn C A) : Decidable (SameRow k k') :=
  Fintype.decidableForallFintype

-- DMN's result, in output column `a`
def Decision.eval {C A : Type} [Fintype C] [Fintype A] (d : Decision C A) (i : Is dmn C)
    (a : A) : Result :=
  match d.table.matching i with
  | [] => .noMatch
  | k :: rest =>
    match d.pick with
    | .unique => if rest.isEmpty then .one (k.asserts a) else .violation
    | .any =>
      if rest.all fun k' => decide (SameRow k k') then .one (k.asserts a) else .violation
    | .first => .one (k.asserts a)
    | .collect => .many ((k :: rest).map (·.asserts a))
    | .ruleOrder => .many ((k :: rest).map (·.asserts a))

/-! ## Checking tables before evaluation -/

-- no two rules of `t`, by position, can match together
def Unique {C A : Type} (t : Table dmn C A) : Prop :=
  t.clauses.Pairwise fun k k' => ¬ k.CoInvocable (fun _ => True) k'

-- matching rules of `t` never disagree in any output column
def AnyValid {C A : Type} (t : Table dmn C A) : Prop :=
  ∀ a, t.Decisive (fun _ => True) a

-- every rule of `t` gives an output in every column, as DMN rules do
def FullRows {C A : Type} (t : Table dmn C A) : Prop :=
  ∀ k ∈ t.clauses, ∀ b, k.asserts b ≠ none

-- two rules can match together iff their tests overlap in every column
theorem coInvocable_iff_overlap {C A : Type} (k k' : Clause dmn C A) :
    k.CoInvocable (fun _ => True) k' ↔ ∀ c, (k.expects c).Overlap (k'.expects c) := by
  rw [Clause.coInvocable_iff]
  simp [Test.Overlap]

instance {C A : Type} [Fintype C] (k k' : Clause dmn C A) :
    Decidable (k.CoInvocable (fun _ => True) k') :=
  decidable_of_iff _ (coInvocable_iff_overlap k k').symm

instance {C A : Type} [Fintype C] (t : Table dmn C A) : Decidable (Unique t) :=
  inferInstanceAs (Decidable (List.Pairwise _ _))

-- a `Unique` table never reports a violation
theorem eval_unique_ne_violation {C A : Type} [Fintype C] [Fintype A] {d : Decision C A}
    (hpick : d.pick = .unique)
    (huniq : Unique d.table)
    (i : Is dmn C) (a : A) :
    d.eval i a ≠ .violation := by
  have hpair : (d.table.matching i).Pairwise fun k k' => ¬ k.CoInvocable (fun _ => True) k' :=
    huniq.sublist List.filter_sublist
  unfold Decision.eval
  split
  · exact Result.noConfusion
  rename_i k rest hmatch
  rw [hpick]
  cases rest with
  | nil => exact Result.noConfusion
  | cons k' rest =>
    rw [hmatch] at hpair
    have hk : k.Invoked i := ((d.table.mem_matching i k).mp (by simp [hmatch])).2
    have hk' : k'.Invoked i := ((d.table.mem_matching i k').mp (by simp [hmatch])).2
    have hnot : ¬ k.CoInvocable (fun _ => True) k' := List.rel_of_pairwise_cons hpair (by simp)
    exact absurd ⟨i, fun _ => trivial, hk, hk'⟩ hnot

-- an `AnyValid` table with full rows never reports a violation
theorem eval_any_ne_violation {C A : Type} [Fintype C] [Fintype A] {d : Decision C A}
    (hpick : d.pick = .any)
    (hvalid : AnyValid d.table)
    (hfull : FullRows d.table)
    (i : Is dmn C) (a : A) :
    d.eval i a ≠ .violation := by
  unfold Decision.eval
  split
  · exact Result.noConfusion
  rename_i k rest hmatch
  rw [hpick]
  simp only
  split
  · exact Result.noConfusion
  rename_i hall
  -- some later matching rule `k'` has a different row
  simp only [List.all_eq_true, decide_eq_true_eq, Classical.not_forall]
    at hall
  obtain ⟨k', hk'rest, hdiff⟩ := hall
  simp only [SameRow, Classical.not_forall] at hdiff
  obtain ⟨b, hb⟩ := hdiff
  have hk : k ∈ d.table.clauses ∧ k.Invoked i :=
    (d.table.mem_matching i k).mp (by simp [hmatch])
  have hk' : k' ∈ d.table.clauses ∧ k'.Invoked i :=
    (d.table.mem_matching i k').mp (by simp [hmatch, hk'rest])
  have hdis : k.Disagree b k' := ⟨hb, hfull k hk.1 b, hfull k' hk'.1 b⟩
  have hco : k.CoInvocable (fun _ => True) k' := ⟨i, fun _ => trivial, hk.2, hk'.2⟩
  exact fun _ => (Table.not_decisive_iff _ d.table b).mpr ⟨k, hk.1, k', hk'.1, hdis, hco⟩
    (hvalid b)

-- `-` passes every value, so a row of `-` is a catch-all
theorem universal_any : dmn.Universal .any :=
  fun _ => trivial

-- with `first`, a catch-all `z` at the end is an else
theorem eval_first_catchAll {C A : Type} [Fintype C] [Fintype A] (t : Table dmn C A)
    {z : Clause dmn C A}
    (hz : ∀ c, z.expects c = .any)
    (i : Is dmn C) (a : A) :
    (⟨t.append ⟨[z]⟩, .first⟩ : Decision C A).eval i a =
      match t.matching i with
      | [] => .one (z.asserts a)
      | k :: _ => .one (k.asserts a) := by
  have hzi : z.Invoked i := z.invoked_of_universal universal_any hz i
  have hmatch : (t.append ⟨[z]⟩).matching i = t.matching i ++ [z] := by
    simp [Table.matching, Table.append, List.filter_append, hzi]
  unfold Decision.eval
  rw [hmatch]
  cases t.matching i <;> rfl

/-! ## A minimal example -/

inductive TicketCond where
  | age
  deriving DecidableEq

instance : Fintype TicketCond where
  elems := {TicketCond.age}
  complete := by
    intro c
    cases c
    simp

inductive TicketAsrt where
  | price
  deriving DecidableEq

instance : Fintype TicketAsrt where
  elems := {TicketAsrt.price}
  complete := by
    intro a
    cases a
    simp

-- a row: age test, price
def priceRule (eAge : Test) (price : Int) : Clause dmn TicketCond TicketAsrt where
  expects
    | .age => eAge
  asserts
    | .price => some (.int price)

-- children 12 and under pay 5, people 12 and over pay 10: age 12 is in both
def ticketBuggy : Table dmn TicketCond TicketAsrt :=
  ⟨[priceRule (.le 12) 5, priceRule (.ge 12) 10]⟩

-- the fix: children under 12 pay 5
def ticketFixed : Table dmn TicketCond TicketAsrt :=
  ⟨[priceRule (.lt 12) 5, priceRule (.ge 12) 10]⟩

-- observed age
def visitor (oAge : Int) : Is dmn TicketCond
  | .age => .int oAge

theorem ticketBuggy_not_unique : ¬ Unique ticketBuggy := by
  decide

-- a 12-year-old matches both rules, so a `unique` decision reports a violation
theorem ticketBuggy_violation :
    (⟨ticketBuggy, .unique⟩ : Decision TicketCond TicketAsrt).eval (visitor 12) .price =
      .violation := by
  decide

theorem ticketFixed_unique : Unique ticketFixed := by
  decide

-- after the fix, no age ever reports a violation
theorem ticketFixed_never_violates (i : Is dmn TicketCond) (a : TicketAsrt) :
    (⟨ticketFixed, .unique⟩ : Decision TicketCond TicketAsrt).eval i a ≠ .violation :=
  eval_unique_ne_violation rfl ticketFixed_unique i a

theorem ticketFixed_twelve :
    (⟨ticketFixed, .unique⟩ : Decision TicketCond TicketAsrt).eval (visitor 12) .price =
      .one (some (.int 10)) := by
  decide

-- under 12 pay 5, 12 to 64 pay 10, and a catch-all meant as "otherwise, pay 8"
def ticketWithDefault : Table dmn TicketCond TicketAsrt :=
  ⟨[priceRule (.lt 12) 5, priceRule (.range 12 64 true true) 10, priceRule .any 8]⟩

theorem ticketWithDefault_not_unique : ¬ Unique ticketWithDefault := by
  decide

-- a 30-year-old matches two rules; a 70-year-old matches only the catch-all
theorem ticketWithDefault_picks :
    (⟨ticketWithDefault, .unique⟩ : Decision TicketCond TicketAsrt).eval (visitor 30) .price =
      .violation ∧
    (⟨ticketWithDefault, .any⟩ : Decision TicketCond TicketAsrt).eval (visitor 30) .price =
      .violation ∧
    (⟨ticketWithDefault, .collect⟩ : Decision TicketCond TicketAsrt).eval (visitor 30) .price =
      .many [some (.int 10), some (.int 8)] ∧
    (⟨ticketWithDefault, .first⟩ : Decision TicketCond TicketAsrt).eval (visitor 30) .price =
      .one (some (.int 10)) ∧
    (⟨ticketWithDefault, .first⟩ : Decision TicketCond TicketAsrt).eval (visitor 70) .price =
      .one (some (.int 8)) := by
  decide

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

instance : Fintype Asrt where
  elems := {Asrt.discount}
  complete := by
    intro a
    cases a
    simp

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

-- no two rules can match together, so the table is valid with `unique`
theorem discount_unique : Unique discount := by
  decide

-- as a `unique` decision it never reports a violation
theorem discount_never_violates (i : Is dmn Cond) (a : Asrt) :
    (⟨discount, .unique⟩ : Decision Cond Asrt).eval i a ≠ .violation :=
  eval_unique_ne_violation rfl discount_unique i a

-- a catch-all meant as "otherwise, no discount"
def withDefault : Table dmn Cond Asrt :=
  discount.append ⟨[rule .any .any 0]⟩

-- it fires next to the business rules, so the discount becomes ambiguous
theorem withDefault_not_decisive : ¬ withDefault.Decisive (fun _ => True) .discount := by
  rw [decisive_iff]
  decide

theorem withDefault_not_unique : ¬ Unique withDefault := by
  decide

-- the same table under each pick, for a business order of 12 and an unknown customer
theorem withDefault_picks :
    (⟨withDefault, .unique⟩ : Decision Cond Asrt).eval (observe "Business" 12) .discount =
      .violation ∧
    (⟨withDefault, .any⟩ : Decision Cond Asrt).eval (observe "Business" 12) .discount =
      .violation ∧
    (⟨withDefault, .first⟩ : Decision Cond Asrt).eval (observe "Business" 12) .discount =
      .one (some (.int 10)) ∧
    (⟨withDefault, .first⟩ : Decision Cond Asrt).eval (observe "Other" 12) .discount =
      .one (some (.int 0)) ∧
    (⟨withDefault, .collect⟩ : Decision Cond Asrt).eval (observe "Business" 12) .discount =
      .many [some (.int 10), some (.int 0)] := by
  decide

-- with `first`, putting the catch-all first changes the answer
theorem first_depends_on_order :
    (⟨⟨rule .any .any 0 :: discount.clauses⟩, .first⟩ : Decision Cond Asrt).eval
      (observe "Business" 12) .discount = .one (some (.int 0)) := by
  decide

/-! ## Loan grade example (Calvanese et al., BPM 2016, Table 1) -/

inductive LoanCond where
  | income | loan
  deriving DecidableEq

instance : Fintype LoanCond where
  elems := {LoanCond.income, LoanCond.loan}
  complete := by
    intro c
    cases c <;> simp

inductive LoanAsrt where
  | grade
  deriving DecidableEq

instance : Fintype LoanAsrt where
  elems := {LoanAsrt.grade}
  complete := by
    intro a
    cases a
    simp

-- a row: annual-income test, loan-size test, grade
def gradeRule (eIncome eLoan : Test) (grade : String) : Clause dmn LoanCond LoanAsrt where
  expects
    | .income => eIncome
    | .loan => eLoan
  asserts
    | .grade => some (.str grade)

def ruleA := gradeRule (.range 0 1000 true true) (.range 0 1000 true true) "VG"
def ruleB := gradeRule (.range 250 750 true true) (.range 4000 5000 true true) "G"
def ruleC := gradeRule (.range 500 1500 true true) (.range 500 3000 true true) "F"
def ruleD := gradeRule (.range 2000 2500 true true) (.range 0 2000 true true) "P"

-- declared unique (U) and complete (C)
def loanGrade : Table dmn LoanCond LoanAsrt := ⟨[ruleA, ruleB, ruleC, ruleD]⟩

-- observed annual income and loan size
def applicant (oIncome oLoan : Int) : Is dmn LoanCond
  | .income => .int oIncome
  | .loan => .int oLoan

-- as reported: A and C overlap, so the table is not unique
theorem loanGrade_A_C_overlap : ruleA.CoInvocable (fun _ => True) ruleC := by
  decide

theorem loanGrade_not_unique : ¬ Unique loanGrade := by
  decide

-- and it is the only overlap: dropping either A or C makes the table unique
theorem loanGrade_only_A_C :
    Unique ⟨[ruleB, ruleC, ruleD]⟩ ∧ Unique ⟨[ruleA, ruleB, ruleD]⟩ := by
  decide

-- A says VG and C says F, so the overlap is also a disagreement
theorem loanGrade_not_decisive : ¬ loanGrade.Decisive (fun _ => True) .grade := by
  rw [decisive_iff]
  decide

-- inside the intersection [500..1000] × [500..1000] evaluation reports a violation
theorem loanGrade_violation :
    (⟨loanGrade, .unique⟩ : Decision LoanCond LoanAsrt).eval (applicant 750 750) .grade =
      .violation := by
  decide

-- as reported: ⟨200, 2000⟩ matches no rule, so the table is not complete
theorem loanGrade_gap :
    (⟨loanGrade, .unique⟩ : Decision LoanCond LoanAsrt).eval (applicant 200 2000) .grade =
      .noMatch := by
  decide

end Maize.DMN
