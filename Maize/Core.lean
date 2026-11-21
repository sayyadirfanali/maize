import Mathlib.Tactic

namespace Maize

/-! ## Definitions -/

structure Logic where
  State : Type                   -- type for states of a Condition
  Mode : Type                    -- type for modes of an Assertion
  hit : State → State → Prop     -- `hit e o` means expected state `e` hit observed state `o`
  absent : Mode                  -- NO assertion

variable (L : Logic) (Condition Assertion : Type)

abbrev Is := Condition → L.State  -- observed state of each condition

structure Clause where
  expects : Condition → L.State   -- expected state of each condition
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
def Is.Satisfies (P : L.State → Prop) (i : Is L Condition) : Prop :=
  ∀ c, P (i c)

-- some `i` satisfying `P` invokes both `k` and `k'`
def Clause.CoInvocable (P : L.State → Prop) (k k' : Clause L Condition Assertion) : Prop :=
  ∃ i : Is L Condition, i.Satisfies P ∧ k.Invoked i ∧ k'.Invoked i

variable (L) in
-- `o'` is at least as precise as `o`: every `e` hitting `o'` hits `o`
def Logic.Refines (o' o : L.State) : Prop :=
  ∀ e, L.hit e o' → L.hit e o

-- `i' c` refines `i c` for every `c`
def Is.Refines (i' i : Is L Condition) : Prop :=
  ∀ c, L.Refines (i' c) (i c)

-- modes asserted for `a` by clauses invoked by `i`, `absent` removed
def Table.execute (t : Table L Condition Assertion) (i : Is L Condition) (a : Assertion)
    [DecidablePred fun k : Clause L Condition Assertion => k.Invoked i] [DecidableEq L.Mode] :
    List L.Mode :=
  ((t.clauses.filter fun k => decide (k.Invoked i)).map (·.asserts a)).filter (· ≠ L.absent)

-- rows of `k` reindexed along `f` (conditions) and `g` (assertions)
def Clause.comap {Condition' Assertion' : Type} (f : Condition' → Condition)
    (g : Assertion' → Assertion) (k : Clause L Condition Assertion) :
    Clause L Condition' Assertion' :=
  ⟨k.expects ∘ f, k.asserts ∘ g⟩

def Table.comap {Condition' Assertion' : Type} (f : Condition' → Condition)
    (g : Assertion' → Assertion) (t : Table L Condition Assertion) :
    Table L Condition' Assertion' :=
  ⟨t.clauses.map (Clause.comap f g)⟩

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
  obtain ⟨m, hm⟩ := hSilent
  obtain ⟨m', hm', hne⟩ := hDeterminate m hm
  exact Or.inr (Or.inr ⟨m, m', hm, hm', hne.symm⟩)

theorem Table.determinate_not_deferred {t : Table L Condition Assertion} {i : Is L Condition}
    {a : Assertion} :
    t.Determinate i a → ¬ t.Deferred i a := by
  intro ⟨m, _, huniq⟩ ⟨n, n', hn, hn', hne⟩
  have hn_eq : n = m := huniq n hn
  have hn'_eq : n' = m := huniq n' hn'
  exact hne (hn_eq.trans hn'_eq.symm)

theorem Table.silent_not_determinate {t : Table L Condition Assertion} {i : Is L Condition}
    {a : Assertion} :
    t.Silent i a → ¬ t.Determinate i a := by
  intro hSilent ⟨m, hm, _⟩
  exact hSilent m hm

theorem Table.silent_not_deferred {t : Table L Condition Assertion} {i : Is L Condition}
    {a : Assertion} :
    t.Silent i a → ¬ t.Deferred i a := by
  intro hSilent ⟨m, _, hm, _, _⟩
  exact hSilent m hm

/-! ## Order and Repetition -/

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

/-! ## Combination and Equivalence -/

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

/-! ## Coinvocation -/

theorem Clause.coInvocable_iff (P : L.State → Prop) (k k' : Clause L Condition Assertion) :
    k.CoInvocable P k' ↔ ∀ c, ∃ o, P o ∧ L.hit (k.expects c) o ∧ L.hit (k'.expects c) o := by
  constructor
  · intro ⟨i, hsat, hinv, hinv'⟩ c
    exact ⟨i c, hsat c, hinv c, hinv' c⟩
  · intro h
    choose i hsat hinv hinv' using h
    exact ⟨i, hsat, hinv, hinv'⟩

/-! ## Precision -/

theorem Logic.Refines.refl (o : L.State) : L.Refines o o :=
  fun _ h => h

theorem Logic.Refines.trans {o₁ o₂ o₃ : L.State} :
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
  intro href ⟨k, hk, hinv, hasserts, hne⟩
  exact ⟨k, hk, hinv.of_refines href, hasserts, hne⟩

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
  intro href ⟨m, m', hm, hm', hne⟩
  exact ⟨m, m', hm.of_refines href, hm'.of_refines href, hne⟩

-- if at most `m` is asserted under `i`, then under the more precise `i'`
-- exactly `m` is asserted, or nothing is
theorem Table.Determinate.of_refines {t : Table L Condition Assertion} {i' i : Is L Condition}
    {a : Assertion} {m : L.Mode} (href : i'.Refines i)
    (huniq : ∀ m', t.Ought i a m' → m' = m) :
    (t.Ought i' a m ∧ ∀ m', t.Ought i' a m' → m' = m) ∨ t.Silent i' a := by
  by_cases h : ∃ n, t.Ought i' a n
  · left
    obtain ⟨n, hn⟩ := h
    rw [huniq n (hn.of_refines href)] at hn
    exact ⟨hn, fun x hx => huniq x (hx.of_refines href)⟩
  · right
    exact fun x hx => h ⟨x, hx⟩

/-! ## Evaluator -/

theorem Table.mem_execute (t : Table L Condition Assertion) (i : Is L Condition) (a : Assertion)
    [DecidablePred fun k : Clause L Condition Assertion => k.Invoked i] [DecidableEq L.Mode]
    (m : L.Mode) :
    m ∈ t.execute i a ↔ t.Ought i a m := by
  simp only [execute, List.mem_filter, List.mem_map, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨k, ⟨hk, hinv⟩, hasserts⟩, hne⟩
    exact ⟨k, hk, hinv, hasserts, hne⟩
  · rintro ⟨k, hk, hinv, hasserts, hne⟩
    exact ⟨⟨k, ⟨hk, hinv⟩, hasserts⟩, hne⟩

/-! ## Renaming -/

theorem Clause.invoked_comap {Condition' Assertion' : Type} {f : Condition' → Condition}
    (hf : Function.Surjective f) (g : Assertion' → Assertion)
    (k : Clause L Condition Assertion) (i : Is L Condition) :
    (k.comap f g).Invoked (i ∘ f) ↔ k.Invoked i := by
  constructor
  · intro hinv c
    obtain ⟨c', rfl⟩ := hf c
    exact hinv c'
  · intro hinv c'
    exact hinv (f c')

theorem Table.ought_comap {Condition' Assertion' : Type} {f : Condition' → Condition}
    (hf : Function.Surjective f) (g : Assertion' → Assertion)
    (t : Table L Condition Assertion) (i : Is L Condition) (a' : Assertion') (m : L.Mode) :
    (t.comap f g).Ought (i ∘ f) a' m ↔ t.Ought i (g a') m := by
  constructor
  · intro ⟨k', hk', hinv, hasserts, hne⟩
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hk'
    exact ⟨k, hk, (k.invoked_comap hf g i).mp hinv, hasserts, hne⟩
  · intro ⟨k, hk, hinv, hasserts, hne⟩
    have hk' : k.comap f g ∈ (t.comap f g).clauses := List.mem_map.mpr ⟨k, hk, rfl⟩
    exact ⟨k.comap f g, hk', (k.invoked_comap hf g i).mpr hinv, hasserts, hne⟩

end Maize
