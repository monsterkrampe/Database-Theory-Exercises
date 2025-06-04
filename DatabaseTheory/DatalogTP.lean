-- YOU CAN OPEN THIS IN AN ONLINE LEAN EDITOR, JUST GO HERE:
-- https://live.lean-lang.org/
-- You will see the code on the left. The panel on the right shows you the proof goal at the bottom and all available entities/hypotheses above. This depends on your cursor position.

-- Some basic Set definition and related notation
def Set (α) := α -> Prop

namespace Set
  def empty : Set α := fun _ => False
  notation:max "∅" => empty

  def element (e : α) (X : Set α) : Prop := X e
  infixr:75 " ∈ " => element

  def union (X Y : Set α) : Set α := fun e => e ∈ X ∨ e ∈ Y
  infixr:65 " ∪ " => union

  def subset (X Y : Set α) : Prop := ∀ e : α, e ∈ X -> e ∈ Y
  infixr:50 " ⊆ " => subset

  theorem empty_always_subset (X : Set α) : empty ⊆ X := by intro e e_mem; simp [element, empty] at e_mem

  theorem subset_refl (X : Set α) : X ⊆ X := by intro _ h; exact h

  theorem subset_trans {a b c : Set α} : a ⊆ b -> b ⊆ c -> a ⊆ c := by
    intro ha hb
    intro e he
    apply hb
    apply ha
    assumption
end Set

-- A very basic definition of Datalog-like rules, which is generic over the used atoms.
-- Read this as: head <- body[0], body[1], ..., body[n]
-- Note that the basic List datastructure in Lean can only respresent finite lists.
structure Rule (Atom : Type u) where
  head : Atom
  body : List Atom

-- The actual tp operator takes a Datalog program (i.e. a list of rules) and a set of Atoms "facts" and returns another set of Atoms.
def tp_operator (rules : List (Rule Atom)) (facts : Set Atom) : Set Atom :=
  -- We describe a function that tells us when an atom should be in the resulting set (this is how we define sets above).
  -- Namely this should be the case, if we can find an appropriate rule to derive the atom a in question from atoms in the given "facts"
  fun a => ∃ r ∈ rules, a = r.head ∧ ∀ b ∈ r.body, b ∈ facts

-- The recursive definition of a particular step of the tp operator.
def tp_step (rules : List (Rule Atom)) : Nat -> Set Atom
-- the 0-th step is the empty set
| .zero => ∅
-- for step "step+1", we take the result for step "step" (tp_step rules step) and then apply the tp operator
| .succ step =>
  let rec_res := tp_step rules step
  tp_operator rules rec_res

-- The union of all steps of the tp operator; i.e. an atom is in this union if there exists a step such that the atom occurs in this step.
def tp_infty (rules : List (Rule Atom)) : Set Atom := fun a => ∃ step, a ∈ tp_step rules step

-- We show that the tp_operator is monotone, i.e. when applied on sets that are subsets of each other, then this subset relation is preserved after the tp_operator is applied.
theorem tp_operator_monotone {rules : List (Rule Atom)} {I J : Set Atom} : I ⊆ J -> tp_operator rules I ⊆ tp_operator rules J := by
  intro subset e e_mem
  -- Membership in the tp_operator result for I means that there is a suitable rule.
  rcases e_mem with ⟨r, r_mem, e_head, body_mem⟩
  -- To argue that the element e is also in the tp_operator result for J, we can use the same rule.
  exists r
  constructor
  . exact r_mem
  constructor
  . exact e_head
  . intro b b_mem; apply subset; apply body_mem; exact b_mem

-- Furthermore, we show that the i-th step is always contained in step i+1
theorem tp_step_subset_sucessor (rules : List (Rule Atom)) (step : Nat) : tp_step rules step ⊆ tp_step rules (step + 1) := by
  -- We show the claim via induction over the step number.
  induction step with
  -- The base case is simple since the empty set if a subset of every set (we showed this in the beginning for sets).
  | zero => apply Set.empty_always_subset
  | succ step ih =>
    -- The induction step follows directly from the tp operator being monotone and the induction hypothesis (ih).
    apply tp_operator_monotone
    exact ih

-- We lift the previous result to tp steps that are an arbitrary number of steps apart (not just a single one).
theorem tp_step_subset_all_sucessors (rules : List (Rule Atom)) (step : Nat) : ∀ diff, tp_step rules step ⊆ tp_step rules (step + diff) := by
  intro diff
  -- this time we induce over the distance between the sets
  induction diff with
  -- the base case is trivial as every set is a subset of itself
  | zero => apply Set.subset_refl
  | succ diff ih =>
    -- we rewrite the goal to have (step + diff) + 1 instead of step + (diff + 1) so that we can apply our previous result
    rw [← Nat.add_assoc]
    -- we just need to use both our previous result and the induction hypothesis; and the fact that the subset relation is transitive
    apply Set.subset_trans
    . exact ih
    . apply tp_step_subset_sucessor

-- We are ready to prove the first part of exercise 8.5, i.e. tp_infty is really a fixed point.
theorem exercise_8_5_1 (rules : List (Rule Atom)) : tp_operator rules (tp_infty rules) = tp_infty rules := by
  -- The first few lines just unfold the result to allow us to show the inclusions in both directions for a particular element a.
  apply funext
  intro a
  apply propext
  constructor
  -- Direction from left to right.
  . intro h
    -- We know that a is in the result of the tp_operator on tp_infty, hence we can get the corresponding rule used to derive a.
    rcases h with ⟨r, r_mem, a_eq, h⟩

    -- We show here that there exists a natural number k such that all body atoms occur in the k-th tp step.
    -- We want to show this via induction on the length of r.body but this is not so simple for technical reasons.
    -- Instead, we show a slightly more general result, which allows the induction. (Don't worry too much about this.)
    have : ∀ (l : List Atom), (∀ e ∈ l, e ∈ tp_infty rules) -> ∃ k, ∀ e ∈ l, e ∈ tp_step rules k := by
      intro l
      induction l with
      -- If the body is empty no element can be part of it so this is trivial.
      | nil => intros; exists 0; intros; contradiction
      -- Lists are linked lists for for the induction step, we get the first list element hd, the rest of the list tl and the induction hypothesis (our result but only for tl).
      | cons hd tl ih =>
        -- We know that all body atoms are in tp_infty.
        intro all_mem_infty

        -- From the induction hypothesis, we can obtain a k such that at least all body element in tl, i.e. all except the first one (hd),
        -- are known to be in step k; we call this k_ih.
        specialize ih (by intro e e_mem; apply all_mem_infty; simp [e_mem])
        rcases ih with ⟨k_ih, ih⟩

        -- For the single hd element, we know that it occurs in tp_infty and thereby by definition, there is also an appropriate step k_hd.
        have hd_mem := all_mem_infty hd (by simp)
        rcases hd_mem with ⟨k_hd, hd_mem⟩

        -- Now we just distiguish two cases, if k_hd is smaller or equal to k_ih, we show that all body elements are in step k_ih,
        -- otherwise, we show that all of them are in step k_hd.
        -- This is where we also need tp_step_subset_all_sucessors from earlier since we do not know how far k_hd and k_ih are apart.
        -- This is a bit technical and verbose; don't very about the details.
        cases Decidable.em (k_hd ≤ k_ih) with
        | inl le =>
          exists k_ih
          intro e e_mem
          rw [List.mem_cons] at e_mem
          -- For each body atom, we still need to distinguish whether it is hd or in tl.
          cases e_mem with
          | inl e_mem =>
            rcases Nat.exists_eq_add_of_le le with ⟨diff, eq⟩
            rw [eq]
            apply tp_step_subset_all_sucessors
            rw [e_mem]
            exact hd_mem
          | inr e_mem => apply ih; exact e_mem
        | inr le =>
          have le := Nat.le_of_not_le le
          exists k_hd
          intro e e_mem
          rw [List.mem_cons] at e_mem
          -- For each body atom, we still need to distinguish whether it is hd or in tl.
          cases e_mem with
          | inl e_mem =>
            rw [e_mem]
            exact hd_mem
          | inr e_mem =>
            rcases Nat.exists_eq_add_of_le le with ⟨diff, eq⟩
            rw [eq]
            apply tp_step_subset_all_sucessors
            apply ih
            exact e_mem

    -- Lastly, we just need to apply our auxiliary result to obtain a step k, where all body atoms occur.
    -- Then we know that a occurs (at the latest) in step k+1.
    specialize this r.body h
    rcases this with ⟨k, h⟩
    exists k+1
    exists r
    -- This concludes the direction from left to right.

  -- Direction from right to left.
  . intro h
    -- Since a is in tp_infty, it needs to be in some step.
    rcases h with ⟨step, h⟩
    cases step with
    -- If step is zero, we obtain a contradiction since a cannot be in the empty set.
    | zero => simp [tp_step, Set.element, Set.empty] at h
    | succ step =>
      -- For the induction step, we make use of monotonicity.
      apply tp_operator_monotone _ a h
      -- All that's left to show is that the tp step at "step" is contained in tp_infty, but this follows directly from the definition.
      intro e e_mem
      exists step

-- For the second part of Exercise 8.5, we show that tp_infty is a subset of each fixed point F. F being a fixed point means that tp_operator rules F = F.
theorem exercise_8_5_2 (rules : List (Rule Atom)) : ∀ F, tp_operator rules F = F -> tp_infty rules ⊆ F := by
  -- We just name F and the hypothesis.
  intro F F_fixed_point

  -- We show a different result, namely we show that each tp step is a subset of F. We can show this via induction on step.
  have : ∀ step, tp_step rules step ⊆ F := by
    intro step
    induction step with
    -- The base case is again trivial as the empty set is of course a subset of F.
    | zero => apply Set.empty_always_subset
    | succ step ih =>
      -- Since F is a fixed point, we can rewrite the goal to show the subset relation to tp(F) instead of F.
      rw [← F_fixed_point]
      -- Now we can invoke monotonicity.
      apply tp_operator_monotone
      -- All that remains is to show that the tp step at "step" is a subset of F but this is exactly the induction hypothesis.
      exact ih

  -- With the auxiliary result "this" in place, we take an arbitrary element a from tp_infty.
  intro a a_mem
  -- a needs to be at some tp_step by definition.
  rcases a_mem with ⟨step, a_mem⟩
  -- Now we can invoke our auxiliary result for exactly this step.
  apply this step
  exact a_mem

