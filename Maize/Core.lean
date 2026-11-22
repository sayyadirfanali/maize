import Mathlib.Tactic

namespace Maize

/-! ## Definitions -/

structure Logic where
  Expected : Type                     -- what a cell of a clause says
  Observed : Type                     -- what a fact says
  Mode : Type                         -- type for modes of an Assertion
  hit : Expected → Observed → Prop    -- `hit e o` means expected `e` hit observed `o`
  absent : Mode                       -- NO assertion

variable (L : Logic) (Condition Assertion : Type)

abbrev Is := Condition → L.Observed  -- observed state of each condition

structure Clause where
  expects : Condition → L.Expected  -- expected state of each condition
  asserts : Assertion → L.Mode    -- produced mode of each assertion

structure Table where
  clauses : List (Clause L Condition Assertion)

variable {L Condition Assertion}

-- every `k.expects c` hits `i c`
def Clause.Invoked (k : Clause L Condition Assertion) (i : Is L Condition) : Prop :=
  ∀ c, L.hit (k.expects c) (i c)

-- `k` is invoked by `i` and asserts `m ≠ absent` for `a`
def Clause.Ought (k : Clause L Condition Assertion) (i : Is L Condition)
    (a : Assertion) (m : L.Mode) : Prop :=
  k.Invoked i ∧ k.asserts a = m ∧ m ≠ L.absent

-- `k.Ought i a m` for some `k ∈ t.clauses`
def Table.Ought (t : Table L Condition Assertion) (i : Is L Condition)
    (a : Assertion) (m : L.Mode) : Prop :=
  ∃ k ∈ t.clauses, k.Ought i a m

-- no `m` for `a`
def Table.Silent (t : Table L Condition Assertion) (i : Is L Condition) (a : Assertion) : Prop :=
  ∀ m, ¬ t.Ought i a m

-- exactly one `m` for `a`
def Table.Determinate (t : Table L Condition Assertion) (i : Is L Condition)
    (a : Assertion) : Prop :=
  ∃ m, t.Ought i a m ∧ ∀ m', t.Ought i a m' → m' = m

-- two different `m`, `m'` for `a`
def Table.Deferred (t : Table L Condition Assertion) (i : Is L Condition)
    (a : Assertion) : Prop :=
  ∃ m m', t.Ought i a m ∧ t.Ought i a m' ∧ m ≠ m'

-- clauses of `t` followed by clauses of `u`
def Table.append (t u : Table L Condition Assertion) : Table L Condition Assertion :=
  ⟨t.clauses ++ u.clauses⟩

-- same `Ought` for every `i`, `a`, `m`
def Table.Equiv (t u : Table L Condition Assertion) : Prop :=
  ∀ i a m, t.Ought i a m ↔ u.Ought i a m

-- every `i c` satisfies `P`
def Is.Satisfies (P : L.Observed → Prop) (i : Is L Condition) : Prop :=
  ∀ c, P (i c)

-- some `i` satisfying `P` invokes both `k` and `k'`
def Clause.CoInvocable (P : L.Observed → Prop) (k k' : Clause L Condition Assertion) : Prop :=
  ∃ i : Is L Condition, i.Satisfies P ∧ k.Invoked i ∧ k'.Invoked i

variable (L) in
-- `o'` is at least as precise as `o`: every `e` hitting `o'` hits `o`
def Logic.Refines (o' o : L.Observed) : Prop :=
  ∀ e, L.hit e o' → L.hit e o

-- `i' c` refines `i c` for every `c`
def Is.Refines (i' i : Is L Condition) : Prop :=
  ∀ c, L.Refines (i' c) (i c)

-- clauses of `t` invoked by `i`, in table order
def Table.matching (t : Table L Condition Assertion) (i : Is L Condition)
    [DecidablePred fun k : Clause L Condition Assertion => k.Invoked i] :
    List (Clause L Condition Assertion) :=
  t.clauses.filter fun k => decide (k.Invoked i)

-- modes asserted for `a` by `t.matching i`, `absent` removed
def Table.execute (t : Table L Condition Assertion) (i : Is L Condition) (a : Assertion)
    [DecidablePred fun k : Clause L Condition Assertion => k.Invoked i] [DecidableEq L.Mode] :
    List L.Mode :=
  ((t.matching i).map (·.asserts a)).filter (· ≠ L.absent)

-- rows of `k` reindexed along `f` (conditions) and `g` (assertions)
def Clause.comap {Condition' Assertion' : Type} (f : Condition' → Condition)
    (g : Assertion' → Assertion) (k : Clause L Condition Assertion) :
    Clause L Condition' Assertion' :=
  ⟨k.expects ∘ f, k.asserts ∘ g⟩

def Table.comap {Condition' Assertion' : Type} (f : Condition' → Condition)
    (g : Assertion' → Assertion) (t : Table L Condition Assertion) :
    Table L Condition' Assertion' :=
  ⟨t.clauses.map (Clause.comap f g)⟩

-- `k` and `k'` assert different modes for `a`, neither absent
def Clause.Disagree (a : Assertion) (k k' : Clause L Condition Assertion) : Prop :=
  k.asserts a ≠ k'.asserts a ∧ k.asserts a ≠ L.absent ∧ k'.asserts a ≠ L.absent

-- no `i` satisfying `P` makes `a` deferred
def Table.Decisive (P : L.Observed → Prop) (t : Table L Condition Assertion)
    (a : Assertion) : Prop :=
  ∀ i : Is L Condition, i.Satisfies P → ¬ t.Deferred i a

variable (L) in
-- `u` hits every state
def Logic.Universal (u : L.Expected) : Prop :=
  ∀ o, L.hit u o

-- expected states mapped by `fE`, modes by `g`
def Clause.map {L' : Logic} (fE : L.Expected → L'.Expected) (g : L.Mode → L'.Mode)
    (k : Clause L Condition Assertion) : Clause L' Condition Assertion :=
  ⟨fE ∘ k.expects, g ∘ k.asserts⟩

def Table.map {L' : Logic} (fE : L.Expected → L'.Expected) (g : L.Mode → L'.Mode)
    (t : Table L Condition Assertion) : Table L' Condition Assertion :=
  ⟨t.clauses.map (Clause.map fE g)⟩

/-! ## Statuses -/

theorem Table.trichotomy {t : Table L Condition Assertion} {i : Is L Condition}
    {a : Assertion} :
    t.Silent i a ∨ t.Determinate i a ∨ t.Deferred i a := by
  by_cases hSilent : t.Silent i a
  · exact Or.inl hSilent
  by_cases hDeterminate : t.Determinate i a
  · exact Or.inr (Or.inl hDeterminate)
  simp only [Table.Silent, Table.Determinate] at hSilent hDeterminate
  push Not at hSilent hDeterminate
  obtain ⟨m, hm⟩ : ∃ m, t.Ought i a m := hSilent
  obtain ⟨m', hm', hne⟩ : ∃ m', t.Ought i a m' ∧ m' ≠ m := hDeterminate m hm
  exact Or.inr (Or.inr ⟨m, m', hm, hm', hne.symm⟩)

theorem Table.determinate_not_deferred {t : Table L Condition Assertion} {i : Is L Condition}
    {a : Assertion} :
    t.Determinate i a → ¬ t.Deferred i a := by
  intro hDeterminate hDeferred
  obtain ⟨m, -, huniq⟩ := hDeterminate
  obtain ⟨n, n', hn, hn', hne⟩ := hDeferred
  have hn_eq : n = m := huniq n hn
  have hn'_eq : n' = m := huniq n' hn'
  exact hne (hn_eq.trans hn'_eq.symm)

theorem Table.silent_not_determinate {t : Table L Condition Assertion} {i : Is L Condition}
    {a : Assertion} :
    t.Silent i a → ¬ t.Determinate i a := by
  intro hSilent hDeterminate
  obtain ⟨m, hm, -⟩ := hDeterminate
  exact hSilent m hm

theorem Table.silent_not_deferred {t : Table L Condition Assertion} {i : Is L Condition}
    {a : Assertion} :
    t.Silent i a → ¬ t.Deferred i a := by
  intro hSilent hDeferred
  obtain ⟨m, -, hm, -, -⟩ := hDeferred
  exact hSilent m hm

/-! ## Order and repetition of clauses -/

theorem Table.ought_congr_mem {t u : Table L Condition Assertion}
    (hmem : ∀ k, k ∈ t.clauses ↔ k ∈ u.clauses)
    (i : Is L Condition) (a : Assertion) (m : L.Mode) :
    t.Ought i a m ↔ u.Ought i a m := by
  constructor
  · intro ⟨k, hk, hought⟩
    exact ⟨k, (hmem k).mp hk, hought⟩
  · intro ⟨k, hk, hought⟩
    exact ⟨k, (hmem k).mpr hk, hought⟩

-- reordering `t.clauses` changes nothing
theorem Table.ought_perm {t u : Table L Condition Assertion}
    (hperm : t.clauses.Perm u.clauses)
    (i : Is L Condition) (a : Assertion) (m : L.Mode) :
    t.Ought i a m ↔ u.Ought i a m :=
  ought_congr_mem (fun _ => hperm.mem_iff) i a m

-- repeating a `k ∈ t.clauses` changes nothing
theorem Table.ought_cons_of_mem {t : Table L Condition Assertion}
    {k : Clause L Condition Assertion} (hk : k ∈ t.clauses)
    (i : Is L Condition) (a : Assertion) (m : L.Mode) :
    (⟨k :: t.clauses⟩ : Table L Condition Assertion).Ought i a m ↔ t.Ought i a m := by
  apply ought_congr_mem
  intro k'
  constructor
  · intro hk'
    rcases List.mem_cons.mp hk' with rfl | hk'
    · exact hk
    · exact hk'
  · intro hk'
    exact List.mem_cons_of_mem k hk'

/-! ## Combination and equivalence -/

theorem Table.ought_append (t u : Table L Condition Assertion) (i : Is L Condition)
    (a : Assertion) (m : L.Mode) :
    (t.append u).Ought i a m ↔ t.Ought i a m ∨ u.Ought i a m := by
  constructor
  · intro ⟨k, hk, hought⟩
    rcases List.mem_append.mp hk with hk | hk
    · exact Or.inl ⟨k, hk, hought⟩
    · exact Or.inr ⟨k, hk, hought⟩
  · rintro (⟨k, hk, hought⟩ | ⟨k, hk, hought⟩)
    · exact ⟨k, List.mem_append.mpr (Or.inl hk), hought⟩
    · exact ⟨k, List.mem_append.mpr (Or.inr hk), hought⟩

theorem Table.Equiv.refl (t : Table L Condition Assertion) : t.Equiv t :=
  fun _ _ _ => Iff.rfl

theorem Table.Equiv.symm {t u : Table L Condition Assertion} : t.Equiv u → u.Equiv t :=
  fun h i a m => (h i a m).symm

theorem Table.Equiv.trans {t u v : Table L Condition Assertion} :
    t.Equiv u → u.Equiv v → t.Equiv v :=
  fun htu huv i a m => (htu i a m).trans (huv i a m)

-- `Equiv` is a congruence for `append`
theorem Table.Equiv.append {t t' u u' : Table L Condition Assertion} :
    t.Equiv t' → u.Equiv u' → (t.append u).Equiv (t'.append u') := by
  intro ht hu i a m
  rw [ought_append, ought_append, ht i a m, hu i a m]

theorem Table.append_comm (t u : Table L Condition Assertion) :
    (t.append u).Equiv (u.append t) := by
  intro i a m
  rw [ought_append, ought_append, or_comm]

theorem Table.append_assoc (t u v : Table L Condition Assertion) :
    ((t.append u).append v).Equiv (t.append (u.append v)) := by
  intro i a m
  simp only [ought_append, or_assoc]

theorem Table.append_self (t : Table L Condition Assertion) : (t.append t).Equiv t := by
  intro i a m
  rw [ought_append, or_self]

/-! ## Co-invocation is decided row by row -/

theorem Clause.coInvocable_iff (P : L.Observed → Prop) (k k' : Clause L Condition Assertion) :
    k.CoInvocable P k' ↔
      ∀ c, ∃ o, P o ∧ L.hit (k.expects c) o ∧ L.hit (k'.expects c) o := by
  constructor
  · intro hco c
    obtain ⟨i, hsat, hinv, hinv'⟩ := hco
    exact ⟨i c, hsat c, hinv c, hinv' c⟩
  · intro hrow
    choose i hsat hinv hinv' using hrow  -- `i c` is the witness `o` for row `c`
    exact ⟨i, hsat, hinv, hinv'⟩

/-! ## Precision -/

theorem Logic.Refines.refl (o : L.Observed) : L.Refines o o :=
  fun _ h => h

theorem Logic.Refines.trans {o₁ o₂ o₃ : L.Observed} :
    L.Refines o₁ o₂ → L.Refines o₂ o₃ → L.Refines o₁ o₃ := by
  intro h₁₂ h₂₃ e he
  exact h₂₃ e (h₁₂ e he)

theorem Is.Refines.refl (i : Is L Condition) : i.Refines i :=
  fun c => Logic.Refines.refl (i c)

theorem Is.Refines.trans {i₁ i₂ i₃ : Is L Condition} :
    i₁.Refines i₂ → i₂.Refines i₃ → i₁.Refines i₃ :=
  fun h₁₂ h₂₃ c => (h₁₂ c).trans (h₂₃ c)

-- invoked by the more precise `i'` → invoked by `i`
theorem Clause.Invoked.of_refines {k : Clause L Condition Assertion} {i' i : Is L Condition} :
    i'.Refines i → k.Invoked i' → k.Invoked i := by
  intro href hinv c
  exact href c (k.expects c) (hinv c)

theorem Table.Ought.of_refines {t : Table L Condition Assertion} {i' i : Is L Condition}
    {a : Assertion} {m : L.Mode} :
    i'.Refines i → t.Ought i' a m → t.Ought i a m := by
  intro href hought
  obtain ⟨k, hk, hinv', hasserts, hne⟩ := hought
  have hinv : k.Invoked i := hinv'.of_refines href
  exact ⟨k, hk, hinv, hasserts, hne⟩

-- silence survives gaining precision
theorem Table.Silent.of_refines {t : Table L Condition Assertion} {i' i : Is L Condition}
    {a : Assertion} :
    i'.Refines i → t.Silent i a → t.Silent i' a := by
  intro href hSilent m hm
  exact hSilent m (hm.of_refines href)

-- gaining precision cannot create a deferral
theorem Table.Deferred.of_refines {t : Table L Condition Assertion} {i' i : Is L Condition}
    {a : Assertion} :
    i'.Refines i → t.Deferred i' a → t.Deferred i a := by
  intro href hDeferred
  obtain ⟨m, m', hm, hm', hne⟩ := hDeferred
  exact ⟨m, m', hm.of_refines href, hm'.of_refines href, hne⟩

-- if at most `m` is asserted under `i`, then under the more precise `i'`
-- exactly `m` is asserted, or nothing is
theorem Table.Determinate.of_refines {t : Table L Condition Assertion} {i' i : Is L Condition}
    {a : Assertion} {m : L.Mode}
    (href : i'.Refines i)
    (huniq : ∀ m', t.Ought i a m' → m' = m) :
    (t.Ought i' a m ∧ ∀ m', t.Ought i' a m' → m' = m) ∨ t.Silent i' a := by
  by_cases hsome : ∃ n, t.Ought i' a n
  · left
    obtain ⟨n, hn⟩ := hsome
    have hnm : n = m := huniq n (hn.of_refines href)
    rw [hnm] at hn
    exact ⟨hn, fun x hx => huniq x (hx.of_refines href)⟩
  · right
    exact fun x hx => hsome ⟨x, hx⟩

/-! ## Executable evaluator -/

theorem Table.mem_matching (t : Table L Condition Assertion) (i : Is L Condition)
    [DecidablePred fun k : Clause L Condition Assertion => k.Invoked i]
    (k : Clause L Condition Assertion) :
    k ∈ t.matching i ↔ k ∈ t.clauses ∧ k.Invoked i := by
  simp only [matching, List.mem_filter, decide_eq_true_eq]

theorem Table.mem_execute (t : Table L Condition Assertion) (i : Is L Condition) (a : Assertion)
    [DecidablePred fun k : Clause L Condition Assertion => k.Invoked i] [DecidableEq L.Mode]
    (m : L.Mode) :
    m ∈ t.execute i a ↔ t.Ought i a m := by
  simp only [execute, List.mem_filter, List.mem_map, mem_matching, decide_eq_true_eq]
  constructor
  · intro ⟨hmem, hne⟩
    obtain ⟨k, ⟨hk, hinv⟩, hasserts⟩ := hmem
    exact ⟨k, hk, hinv, hasserts, hne⟩
  · intro hought
    obtain ⟨k, hk, hinv, hasserts, hne⟩ := hought
    exact ⟨⟨k, ⟨hk, hinv⟩, hasserts⟩, hne⟩

-- `execute` returning exactly `[m]` means determinate
theorem Table.determinate_of_execute {t : Table L Condition Assertion} {i : Is L Condition}
    {a : Assertion}
    [DecidablePred fun k : Clause L Condition Assertion => k.Invoked i] [DecidableEq L.Mode]
    {m : L.Mode}
    (hexec : t.execute i a = [m]) :
    t.Determinate i a := by
  have hiff : ∀ m', t.Ought i a m' ↔ m' = m := by
    intro m'
    rw [← t.mem_execute i a m', hexec, List.mem_singleton]
  exact ⟨m, (hiff m).mpr rfl, fun m' hm' => (hiff m').mp hm'⟩

/-! ## Renaming conditions and assertions -/

theorem Clause.invoked_comap {Condition' Assertion' : Type} {f : Condition' → Condition}
    (hf : Function.Surjective f)
    (g : Assertion' → Assertion) (k : Clause L Condition Assertion) (i : Is L Condition) :
    (k.comap f g).Invoked (i ∘ f) ↔ k.Invoked i := by
  constructor
  · intro hinv c
    obtain ⟨c', rfl⟩ := hf c
    exact hinv c'
  · intro hinv c'
    exact hinv (f c')

theorem Table.ought_comap {Condition' Assertion' : Type} {f : Condition' → Condition}
    (hf : Function.Surjective f)
    (g : Assertion' → Assertion) (t : Table L Condition Assertion) (i : Is L Condition)
    (a' : Assertion') (m : L.Mode) :
    (t.comap f g).Ought (i ∘ f) a' m ↔ t.Ought i (g a') m := by
  constructor
  · intro hought
    obtain ⟨k', hk', hinv', hasserts, hne⟩ := hought
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hk'  -- `k'` is `k.comap f g`
    have hinv : k.Invoked i := (k.invoked_comap hf g i).mp hinv'
    exact ⟨k, hk, hinv, hasserts, hne⟩
  · intro hought
    obtain ⟨k, hk, hinv, hasserts, hne⟩ := hought
    have hk' : k.comap f g ∈ (t.comap f g).clauses := List.mem_map.mpr ⟨k, hk, rfl⟩
    have hinv' : (k.comap f g).Invoked (i ∘ f) := (k.invoked_comap hf g i).mpr hinv
    exact ⟨k.comap f g, hk', hinv', hasserts, hne⟩

/-! ## Translating tables between logics -/

-- `fE` and `fO` keep hit: invocation is unchanged
theorem Clause.invoked_map {L' : Logic} {fE : L.Expected → L'.Expected}
    {fO : L.Observed → L'.Observed}
    (hf : ∀ e o, L'.hit (fE e) (fO o) ↔ L.hit e o)
    (g : L.Mode → L'.Mode) (k : Clause L Condition Assertion) (i : Is L Condition) :
    (k.map fE g).Invoked (fO ∘ i) ↔ k.Invoked i :=
  forall_congr' fun c => hf (k.expects c) (i c)

theorem Table.ought_map {L' : Logic} {fE : L.Expected → L'.Expected}
    {fO : L.Observed → L'.Observed} {g : L.Mode → L'.Mode}
    (hf : ∀ e o, L'.hit (fE e) (fO o) ↔ L.hit e o)    -- `fE`, `fO` keep hit
    (hg : Function.Injective g)
    (habsent : ∀ m, g m = L'.absent ↔ m = L.absent)    -- `g` keeps `absent`
    (t : Table L Condition Assertion) (i : Is L Condition) (a : Assertion) (m : L.Mode) :
    (t.map fE g).Ought (fO ∘ i) a (g m) ↔ t.Ought i a m := by
  constructor
  · intro hought
    obtain ⟨k', hk', hinv', hasserts, hne⟩ := hought
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hk'  -- `k'` is `k.map fE g`
    have hinv : k.Invoked i := (k.invoked_map hf g i).mp hinv'
    have hm : k.asserts a = m := hg hasserts
    have hm_abs : m ≠ L.absent := fun h => hne ((habsent m).mpr h)
    exact ⟨k, hk, hinv, hm, hm_abs⟩
  · intro hought
    obtain ⟨k, hk, hinv, hasserts, hne⟩ := hought
    have hk' : k.map fE g ∈ (t.map fE g).clauses := List.mem_map.mpr ⟨k, hk, rfl⟩
    have hinv' : (k.map fE g).Invoked (fO ∘ i) := (k.invoked_map hf g i).mpr hinv
    have hm : (k.map fE g).asserts a = g m := congrArg g hasserts
    have hm_abs : g m ≠ L'.absent := fun h => hne ((habsent m).mp h)
    exact ⟨k.map fE g, hk', hinv', hm, hm_abs⟩

/-! ## Choice points come from pairs of clauses -/

-- `a` has a choice point within `P` iff two clauses disagreeing on `a` can fire together
theorem Table.not_decisive_iff (P : L.Observed → Prop) (t : Table L Condition Assertion)
    (a : Assertion) :
    ¬ t.Decisive P a ↔
      ∃ k ∈ t.clauses, ∃ k' ∈ t.clauses, k.Disagree a k' ∧ k.CoInvocable P k' := by
  constructor
  · intro hnot
    unfold Decisive at hnot
    push Not at hnot
    obtain ⟨i, hsat, hDeferred⟩ := hnot
    obtain ⟨m, m', hm, hm', hne⟩ := hDeferred
    obtain ⟨k, hk, hinv, rfl, hm_abs⟩ := hm      -- `m` is `k.asserts a`
    obtain ⟨k', hk', hinv', rfl, hm'_abs⟩ := hm'  -- `m'` is `k'.asserts a`
    have hdis : k.Disagree a k' := ⟨hne, hm_abs, hm'_abs⟩
    have hco : k.CoInvocable P k' := ⟨i, hsat, hinv, hinv'⟩
    exact ⟨k, hk, k', hk', hdis, hco⟩
  · intro hpair hdec
    obtain ⟨k, hk, k', hk', hdis, hco⟩ := hpair
    obtain ⟨hne, hm_abs, hm'_abs⟩ := hdis
    obtain ⟨i, hsat, hinv, hinv'⟩ := hco
    have hm : t.Ought i a (k.asserts a) := ⟨k, hk, hinv, rfl, hm_abs⟩
    have hm' : t.Ought i a (k'.asserts a) := ⟨k', hk', hinv', rfl, hm'_abs⟩
    exact hdec i hsat ⟨k.asserts a, k'.asserts a, hm, hm', hne⟩

-- if a row can be met by both `e` and `e'` exactly when `R e e'`,
-- `a` is decisive iff every disagreeing pair has a row where `R` fails
theorem Table.decisive_iff_rows {P : L.Observed → Prop} {R : L.Expected → L.Expected → Prop}
    (hrow : ∀ e e', (∃ o, P o ∧ L.hit e o ∧ L.hit e' o) ↔ R e e')
    (t : Table L Condition Assertion) (a : Assertion) :
    t.Decisive P a ↔
      ∀ k ∈ t.clauses, ∀ k' ∈ t.clauses,
        k.Disagree a k' → ∃ c, ¬ R (k.expects c) (k'.expects c) := by
  have hco_iff : ∀ k k' : Clause L Condition Assertion,
      k.CoInvocable P k' ↔ ∀ c, R (k.expects c) (k'.expects c) := by
    intro k k'
    rw [Clause.coInvocable_iff]
    exact forall_congr' fun c => hrow (k.expects c) (k'.expects c)
  constructor
  · intro hdec k hk k' hk' hdis
    by_contra hno
    push Not at hno
    have hco : k.CoInvocable P k' := (hco_iff k k').mpr hno
    have hnot : ¬ t.Decisive P a :=
      (not_decisive_iff P t a).mpr ⟨k, hk, k', hk', hdis, hco⟩
    exact hnot hdec
  · intro hpairs
    by_contra hnot
    obtain ⟨k, hk, k', hk', hdis, hco⟩ := (not_decisive_iff P t a).mp hnot
    have hrows : ∀ c, R (k.expects c) (k'.expects c) := (hco_iff k k').mp hco
    obtain ⟨c, hclash⟩ := hpairs k hk k' hk' hdis
    exact hclash (hrows c)

/-! ## Catch-all clauses -/

-- a clause expecting a universal state everywhere is invoked by every `i`
theorem Clause.invoked_of_universal {u : L.Expected}
    (hu : L.Universal u)
    (k : Clause L Condition Assertion)
    (hk : ∀ c, k.expects c = u)
    (i : Is L Condition) :
    k.Invoked i := by
  intro c
  rw [hk c]
  exact hu (i c)

-- a catch-all `z` disagreeing with an invocable `k` creates a choice point
theorem Table.not_decisive_of_catchAll {P : L.Observed → Prop}
    {t : Table L Condition Assertion} {a : Assertion} {u : L.Expected}
    {z k : Clause L Condition Assertion}
    (hu : L.Universal u)
    (hz : z ∈ t.clauses)
    (hzu : ∀ c, z.expects c = u)                                -- `z` is a catch-all
    (hk : k ∈ t.clauses)
    (hdis : z.Disagree a k)
    (hinv : ∃ i : Is L Condition, i.Satisfies P ∧ k.Invoked i) :  -- `k` can fire within `P`
    ¬ t.Decisive P a := by
  obtain ⟨i, hsat, hki⟩ := hinv
  have hzi : z.Invoked i := z.invoked_of_universal hu hzu i
  have hco : z.CoInvocable P k := ⟨i, hsat, hzi, hki⟩
  exact (not_decisive_iff P t a).mpr ⟨z, hz, k, hk, hdis, hco⟩

end Maize
