import GlimpseOfLean.Library.Basic

/-
In this file we manipulate the elementary definition of limits of
sequences of real numbers.
mathlib has a much more general definition of limits, but here
we want to practice using the logical operators and relations
covered in the previous files.
-/

/-
Before we start on, let us make sure Lean doesn't need so much help to
prove equalities or inequalities that linearly follow from known
equalities and inequalities. This is the job of the linear arithmetic
tactic: `linarith`.
-/

example (a b : ℝ) (hb : 0 ≤ b) : a ≤ a + b := by linarith

/-
Let's prove some exercises using `linarith`.
-/

example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b := by {
  linarith
}

example (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d) : a + c ≤ b + d := by {
  linarith
}

/-
A sequence `u` is a function from `ℕ` to `ℝ`, hence Lean says
`u : ℕ → ℝ`
The definition we'll be using is:

-- Definition of « u tends to l »
`def seq_limit (u : ℕ → ℝ) (l : ℝ) := ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε`

Note the use of `∀ ε > 0, _` which is an abbreviation of
`∀ ε, ε > 0 → _ `

In particular, a statement like `h : ∀ ε > 0, _`
can be specialized to a given `ε₀` by
  `specialize h ε₀ hε₀`
where `hε₀` is a proof of `ε₀ > 0`.

Also note that, wherever Lean expects some proof term, we can
start a tactic mode proof using the keyword `by`.
For instance, if the local context contains:

δ : ℝ
δ_pos : δ > 0
h : ∀ ε > 0, _

then we can specialize h to the real number δ/2 using:
  `specialize h (δ/2) (by linarith)`
where `by linarith` will provide the proof of `δ/2 > 0` expected by Lean.
-/

/- If u is constant with value l then u tends to l.
Hint: `simp` can rewrite `|1 - 1|` to `0` -/
example (h : ∀ n, u n = l) : seq_limit u l := by {
  intros ε ε_pos
  use 0
  intros n _
  simp [h]
  linarith
}


/- When dealing with absolute values, we'll use lemmas:

`abs_sub_comm (x y : ℝ) : |x - y| = |y - x|`

`abs_le {x y : ℝ} : |x| ≤ y ↔ -y ≤ x ∧ x ≤ y`

We will also use variants of the triangle inequality

`abs_add (x y : ℝ) : |x + y| ≤ |x| + |y|`
or
`abs_sub_le  (a c b : ℝ) : |a - b| ≤ |a - c| + |c - b|`
or the primed version:
`abs_sub_le' (a c b : ℝ) : |a - b| ≤ |a - c| + |b - c|`
-/

-- Assume `l > 0`. Then `u` tends to `l` implies `u n ≥ l/2` for large enough `n`
example (h : seq_limit u l) (hl : l > 0) :
    ∃ N, ∀ n ≥ N, u n ≥ l/2 := by {
  specialize h (l/2) (by linarith)
  obtain ⟨N, hN⟩ := h
  use N
  intros n hn
  specialize hN n hn
  have := abs_le.mp hN
  linarith
}


/-
When dealing with max, you can use

`ge_max_iff (p q r) : r ≥ max p q ↔ r ≥ p ∧ r ≥ q`

`le_max_left p q : p ≤ max p q`

`le_max_right p q : q ≤ max p q`

Let's see an example.
-/

-- If `u` tends to `l` and `v` tends `l'` then `u+v` tends to `l+l'`
example (hu : seq_limit u l) (hv : seq_limit v l') :
    seq_limit (u + v) (l + l') := by {
  intros ε ε_pos
  rcases hu (ε/2) (by linarith) with ⟨N₁, hN₁⟩
  rcases hv (ε/2) (by linarith) with ⟨N₂, hN₂⟩
  use max N₁ N₂
  intros n hn
  have : n ≥ N₁ := by exact le_of_max_le_left hn
  rw [ge_max_iff] at hn
  rcases hn with ⟨hn₁, hn₂⟩
  have fact₁ : |u n - l| ≤ ε/2
  · exact hN₁ n (by linarith)
  have fact₂ : |v n - l'| ≤ ε/2
  · exact hN₂ n (by linarith)

  calc
    |(u + v) n - (l + l')| = |u n + v n - (l + l')|   := rfl
    _ = |(u n - l) + (v n - l')|                      := by ring
    _ ≤ |u n - l| + |v n - l'|                        := by apply abs_add
    _ ≤ ε                                             := by linarith [fact₁, fact₂]
}


/- Let's do something similar: the squeezing theorem. -/
example (hu : seq_limit u l) (hw : seq_limit w l) (h : ∀ n, u n ≤ v n) (h' : ∀ n, v n ≤ w n) :
    seq_limit v l := by {
  intros ε ε_pos
  have ⟨N₁, hN₁⟩ := hu ε ε_pos
  have ⟨N₂, hN₂⟩ := hw ε ε_pos
  use max N₁ N₂
  intros n hn
  rw [ge_max_iff] at hn
  have ub : v n - l ≤ ε := by calc
    v n - l ≤ w n - l := by simp [h' n]
    _ ≤ ε := (abs_le.mp (hN₂ n (by linarith))).right
  have lb : -ε ≤ v n - l := by calc
    -ε ≤ u n - l := (abs_le.mp (hN₁ n (by linarith))).left
    _ ≤ v n - l := by simp [h n]
  exact abs_le.mpr ⟨lb, ub⟩
}



/- In the next exercise, we'll use

`eq_of_abs_sub_le_all (x y : ℝ) : (∀ ε > 0, |x - y| ≤ ε) → x = y`

Recall we listed three variations on the triangle inequality at the beginning of this file.
-/

-- A sequence admits at most one limit. You will be able to use that lemma in the following
-- exercises.
lemma uniq_limit : seq_limit u l → seq_limit u l' → l = l' := by {
  intros hl hl'
  apply eq_of_abs_sub_le_all
  intros ε ε_pos
  have ⟨N, hN⟩ := hl (ε/2) (by linarith)
  have ⟨N', hN'⟩ := hl' (ε/2) (by linarith)
  let N₀ := max N N'
  specialize hN N₀ (by apply le_max_left)
  specialize hN' N₀ (by apply le_max_right)
  calc
    |l - l'| ≤ |l - u N₀| + |u N₀ - l'| := by apply abs_sub_le
    _ ≤ ε/2 + ε/2 := by rw [abs_sub_comm]; linarith
    _ = ε := by ring
}



/-
Let's now practice deciphering definitions before proving.
-/

def non_decreasing (u : ℕ → ℝ) := ∀ n m, n ≤ m → u n ≤ u m

def is_seq_sup (M : ℝ) (u : ℕ → ℝ) :=
(∀ n, u n ≤ M) ∧ ∀ ε > 0, ∃ n₀, u n₀ ≥ M - ε

example (M : ℝ) (h : is_seq_sup M u) (h' : non_decreasing u) : seq_limit u M := by {
  intros ε ε_pos
  obtain ⟨n₀, hn₀⟩ := h.right ε ε_pos
  use n₀
  intros n hn
  apply abs_le.mpr
  constructor
  · linarith [h' n₀ n hn]
  · linarith [h.left n]
}

/-
We will now play with subsequences.

The new definition we will use is that `φ : ℕ → ℕ` is an extraction
if it is (strictly) increasing.

`def extraction (φ : ℕ → ℕ) := ∀ n m, n < m → φ n < φ m`

In the following, `φ` will always denote a function from `ℕ` to `ℕ`.

The next lemma is proved by an easy induction, but we haven't seen induction
in this tutorial. If you did the natural number game then you can delete
the proof below and try to reconstruct it.
-/
/-- An extraction is greater than id -/
lemma id_le_extraction' : extraction φ → ∀ n, n ≤ φ n := by {
  intros hyp n
  induction n with
  | zero =>  exact Nat.zero_le _
  | succ n ih => exact Nat.succ_le_of_lt (by linarith [hyp n (n+1) (by linarith)])
}


/-
In the exercise, we use `∃ n ≥ N, ...` which is the abbreviation of
`∃ n, n ≥ N ∧ ...`.
-/

/-- Extractions take arbitrarily large values for arbitrarily large
inputs. -/
lemma extraction_ge : extraction φ → ∀ N N', ∃ n ≥ N', φ n ≥ N := by {
  intros hφ N N'
  use max N N'
  have := id_le_extraction' hφ (max N N')
  constructor
  · exact le_max_right N N'
  · linarith [le_max_left N N']
}

/- A real number `a` is a cluster point of a sequence `u`
if `u` has a subsequence converging to `a`.

`def cluster_point (u : ℕ → ℝ) (a : ℝ) := ∃ φ, extraction φ ∧ seq_limit (u ∘ φ) a`
-/


/-- If `a` is a cluster point of `u` then there are values of
`u` arbitrarily close to `a` for arbitrarily large input. -/
lemma near_cluster :
  cluster_point u a → ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε := by {
  intros u_at_a ε ε_pos N
  rcases u_at_a with ⟨φ, hφ, hlim⟩
  rcases hlim ε ε_pos with ⟨N', hN'⟩
  rcases extraction_ge hφ N N' with ⟨n', hn', hφn'⟩
  use φ n', hφn', hN' n' hn'
}


/-- If `u` tends to `l` then its subsequences tend to `l`. -/
lemma subseq_tendsto_of_tendsto' (h : seq_limit u l) (hφ : extraction φ) :
seq_limit (u ∘ φ) l := by {
  intros ε ε_pos
  rcases h ε ε_pos with ⟨N, hN⟩
  use N
  intros n hn
  exact hN (φ n) (by linarith [id_le_extraction' hφ n])
}

/-- If `u` tends to `l` all its cluster points are equal to `l`. -/
lemma cluster_limit (hl : seq_limit u l) (ha : cluster_point u a) : a = l := by {
  rcases ha with ⟨φ, hφ, hlim⟩
  apply uniq_limit
  . exact hlim
  . exact subseq_tendsto_of_tendsto' hl hφ
}

/-- Cauchy_sequence sequence -/
def CauchySequence (u : ℕ → ℝ) :=
  ∀ ε > 0, ∃ N, ∀ p q, p ≥ N → q ≥ N → |u p - u q| ≤ ε

example : (∃ l, seq_limit u l) → CauchySequence u := by {
  rintro ⟨l, hl⟩ ε ε_pos
  rcases hl (ε/2) (by linarith) with ⟨N, hN⟩
  use N
  intros p q hp hq
  linarith [hN p hp, hN q hq, abs_sub_le' (u p) l (u q)]
}

/-
In the next exercise, you can reuse
 near_cluster : cluster_point u a → ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε
-/

example (hu : CauchySequence u) (hl : cluster_point u l) : seq_limit u l := by
  intros ε ε_pos
  rcases hu (ε/2) (by linarith) with ⟨N, hN⟩
  rcases near_cluster hl (ε/2) (by linarith) N with ⟨n, hn, hun⟩
  use N
  intros m hm
  specialize hN m n hm hn
  linarith [abs_sub_le (u m) (u n) l]
