/-
A2a_S3a_WindowProof (L7_8, round 4): proof of the core bijection of `s3_reindex`
(`s3_window_lines_pf`, same statement as `s3_window_lines`).
Each window point `x = b/q (mod 1)` has a unique representative `B/q ∈ [θ − δ/2, θ + δ/2]` (`δ < 1`), `B = b + q·round(θ − b/q)`;
`j = Br − aq`, `k = r′B − a′q` (Step 0). `j = 0` iff the representative is `a/r` (the spike); otherwise `(j, k)` is a
primitive pair on a line `0 < |j| ≤ M` with `q = rk − r′j ∈ I_j`, and conversely.
-/
import ZetaShell.Lemma2.A2a_S3a_WindowAux
import ZetaShell.Skeleton.A2a_S3a_Window
import ZetaShell.Lemma2.A2a_S0_Lines

noncomputable section
open scoped BigOperators

namespace ZetaShell
namespace TrackF

theorem s3_window_lines_pf (F : Fam) (Q r : ℕ) (a a' r' : ℤ) (η δ : ℝ) (hQ : 2 ≤ Q) (hr : 1 ≤ r) (hrQ : r ≤ Q)
    (hdet : a * r' - a' * (r : ℤ) = 1) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∑ x ∈ fareyWin Q ((a : ℝ) / r + η) δ, fareyWeight F Q x
      = spike F Q r η δ + ∑ j ∈ lineSet (lineM Q r η δ),
          ∑ k ∈ Finset.Icc ⌈((lineIv Q r j η δ).1 + r' * j) / (r : ℤ)⌉ ⌊((lineIv Q r j η δ).2 + r' * j) / (r : ℤ)⌋,
            (if Int.gcd k j = 1 then ZetaShell.OmegaW Q (F.omega Q) ((r : ℤ) * k - r' * j).toNat else 0) := by
  classical
  set θ := (a : ℝ) / r + η with hθ
  have hr0 : (0 : ℤ) < r := by exact_mod_cast hr
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hrRZ : ((r : ℤ) : ℝ) = (r : ℝ) := by push_cast; rfl
  have hcopar : IsCoprime a (r : ℤ) := ⟨r', -a', by linear_combination hdet⟩
  -- representative data
  set mm : ((_ : ℕ) × ℕ) → ℤ := fun x => round (θ - fareyPt x) with hmm
  set BB : ((_ : ℕ) × ℕ) → ℤ := fun x => (x.2 : ℤ) + (x.1 : ℤ) * mm x with hBB
  set JJ : ((_ : ℕ) × ℕ) → ℤ := fun x => BB x * r - a * x.1 with hJJ
  set KK : ((_ : ℕ) × ℕ) → ℤ := fun x => r' * BB x - a' * x.1 with hKK
  have hq_of : ∀ x : (_ : ℕ) × ℕ, (r : ℤ) * KK x - r' * JJ x = x.1 := by
    intro x; simp only [hKK, hJJ]; linear_combination (x.1 : ℤ) * hdet
  have hB_of : ∀ x : (_ : ℕ) × ℕ, a * KK x - a' * JJ x = BB x := by
    intro x; simp only [hKK, hJJ]; linear_combination (BB x) * hdet
  have hBq : ∀ x ∈ fareyIdx Q, (BB x : ℝ) / x.1 = fareyPt x + mm x := by
    intro x hx
    have hq : (0 : ℝ) < x.1 := by exact_mod_cast (mem_fareyIdx.mp hx).1.1
    simp only [hBB, fareyPt]; push_cast; field_simp
  have hW : ∀ x ∈ fareyWin Q θ δ, x ∈ fareyIdx Q ∧ |(BB x : ℝ) / x.1 - θ| ≤ δ / 2 := by
    intro x hx
    unfold fareyWin at hx
    obtain ⟨hxI, hxd⟩ := Finset.mem_filter.mp hx
    refine ⟨hxI, ?_⟩
    rw [hBq x hxI]
    have e : fareyPt x + (mm x : ℝ) - θ = -((θ - fareyPt x) - round (θ - fareyPt x)) := by
      simp only [hmm]; ring
    rw [e, abs_neg]
    calc |(θ - fareyPt x) - round (θ - fareyPt x)| ≤ distZ (θ - fareyPt x) := abs_sub_round_le_distZ _
      _ = distZ (fareyPt x - θ) := distZ_sub_comm _ _
      _ ≤ δ / 2 := hxd
  have hcopBq : ∀ x ∈ fareyIdx Q, IsCoprime (BB x) (x.1 : ℤ) := by
    intro x hx
    have h := (mem_fareyIdx.mp hx).2.2
    have h' : IsCoprime (x.2 : ℤ) (x.1 : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr (by exact_mod_cast h)
    simp only [hBB]
    exact h'.add_mul_left_left (mm x)
  -- the window membership from a representative
  have hwin_of : ∀ x ∈ fareyIdx Q, ∀ n : ℤ, |fareyPt x + n - θ| ≤ δ / 2 → x ∈ fareyWin Q θ δ := by
    intro x hx n hn
    unfold fareyWin
    rw [Finset.mem_filter]
    refine ⟨hx, le_trans ?_ hn⟩
    have := distZ_le (fareyPt x - θ) (-n)
    push_cast at this
    rwa [show fareyPt x - θ - -(n : ℝ) = fareyPt x + n - θ by ring] at this
  -- the spike point
  have hJ0 : ∀ x ∈ fareyWin Q θ δ, JJ x = 0 → x.1 = r ∧ BB x = a := by
    intro x hx hj0
    have hxI := (hW x hx).1
    have hq1 : 1 ≤ x.1 := (mem_fareyIdx.mp hxI).1.1
    have hrel : BB x * r = a * x.1 := by simp only [hJJ] at hj0; linarith
    have h1 : (r : ℤ) ∣ (x.1 : ℤ) := by
      have : (r : ℤ) ∣ a * x.1 := ⟨BB x, by linarith⟩
      exact (hcopar.symm).dvd_of_dvd_mul_left this
    have h2 : (x.1 : ℤ) ∣ (r : ℤ) := by
      have : (x.1 : ℤ) ∣ BB x * r := ⟨a, by linarith⟩
      exact ((hcopBq x hxI).symm).dvd_of_dvd_mul_left this
    have hqr : (x.1 : ℤ) = r := Int.dvd_antisymm (by positivity) (by positivity) h2 h1
    have hqrN : x.1 = r := by exact_mod_cast hqr
    refine ⟨hqrN, ?_⟩
    rw [hqr] at hrel
    have : (BB x - a) * r = 0 := by linarith
    have := (mul_eq_zero.mp this).resolve_right (by omega)
    linarith
  have hsplit := Finset.sum_filter_add_sum_filter_not (fareyWin Q θ δ) (fun x => JJ x = 0)
    (fun x => fareyWeight F Q x)
  rw [← hsplit]
  congr 1
  · -- the spike
    have hm0 : 0 ≤ a % (r : ℤ) := Int.emod_nonneg a (by omega)
    have hmlt : a % (r : ℤ) < r := Int.emod_lt_of_pos a hr0
    have hmn : (((a % (r : ℤ)).toNat : ℕ) : ℤ) = a % (r : ℤ) := Int.toNat_of_nonneg hm0
    set x0 : (_ : ℕ) × ℕ := ⟨r, (a % (r : ℤ)).toNat⟩ with hx0
    have hx0I : x0 ∈ fareyIdx Q := by
      rw [mem_fareyIdx]
      show (1 ≤ r ∧ r ≤ Q) ∧ (a % (r : ℤ)).toNat < r ∧ Nat.Coprime (a % (r : ℤ)).toNat r
      refine ⟨⟨hr, hrQ⟩, by omega, ?_⟩
      rw [Nat.Coprime, ← Int.gcd_natCast_natCast, hmn, Int.gcd_emod]
      exact Int.isCoprime_iff_gcd_eq_one.mp hcopar
    have hpt0 : fareyPt x0 + ((a / (r : ℤ) : ℤ) : ℝ) = (a : ℝ) / r := by
      have hd : a % (r : ℤ) = a - (r : ℤ) * (a / (r : ℤ)) := Int.emod_def a r
      have hd' : (((a % (r : ℤ)).toNat : ℕ) : ℝ) = (a : ℝ) - (r : ℝ) * ((a / (r : ℤ) : ℤ) : ℝ) := by
        have : ((((a % (r : ℤ)).toNat : ℕ) : ℤ) : ℝ) = ((a - (r : ℤ) * (a / (r : ℤ)) : ℤ) : ℝ) := by rw [hmn, hd]
        push_cast at this ⊢; linarith
      simp only [hx0, fareyPt]
      rw [hd']
      field_simp
      ring
    have hfilt : ∀ x, x ∈ (fareyWin Q θ δ).filter (fun x => JJ x = 0) ↔ (x = x0 ∧ |η| ≤ δ / 2) := by
      intro x
      rw [Finset.mem_filter]
      constructor
      · rintro ⟨hx, hj0⟩
        obtain ⟨hq, hB⟩ := hJ0 x hx hj0
        have hxI := (hW x hx).1
        have hx2lt : x.2 < x.1 := (mem_fareyIdx.mp hxI).2.1
        have hx2 : ((x.2 : ℕ) : ℤ) = a % (r : ℤ) := by
          have e1 : a = (x.2 : ℤ) + (r : ℤ) * mm x := by rw [← hB]; simp only [hBB, hq]
          rw [e1, Int.add_mul_emod_self_left]
          have : (x.2 : ℤ) < (x.1 : ℤ) := by exact_mod_cast hx2lt
          rw [hq] at this
          exact (Int.emod_eq_of_lt (Int.natCast_nonneg _) this).symm
        have hxeq : x = x0 := by
          apply Sigma.ext hq
          apply heq_of_eq
          show x.2 = (a % (r : ℤ)).toNat
          omega
        refine ⟨hxeq, ?_⟩
        have h1 := (hW x hx).2
        rw [hB, hq] at h1
        rw [hθ] at h1
        have : (a : ℝ) / r - ((a : ℝ) / r + η) = -η := by ring
        rw [this, abs_neg] at h1
        exact h1
      · rintro ⟨rfl, hη⟩
        have hin : x0 ∈ fareyWin Q θ δ := hwin_of x0 hx0I (a / (r : ℤ)) (by
          rw [hpt0, hθ, show (a : ℝ) / r - ((a : ℝ) / r + η) = -η by ring, abs_neg]; exact hη)
        refine ⟨hin, ?_⟩
        have h1 := (hW x0 hin).2
        rw [hBq x0 hx0I] at h1
        have hmm0 : mm x0 = a / (r : ℤ) := int_eq_of_close (fareyPt x0) θ δ hδ1 _ _ h1 (by
          rw [hpt0, hθ, show (a : ℝ) / r - ((a : ℝ) / r + η) = -η by ring, abs_neg]; exact hη)
        have hBB0 : BB x0 = a := by
          show ((x0.2 : ℕ) : ℤ) + ((x0.1 : ℕ) : ℤ) * mm x0 = a
          rw [hmm0]
          show (((a % (r : ℤ)).toNat : ℕ) : ℤ) + (r : ℤ) * (a / (r : ℤ)) = a
          rw [hmn, Int.emod_def]; ring
        show BB x0 * r - a * ((x0.1 : ℕ) : ℤ) = 0
        rw [hBB0]
        show a * r - a * (r : ℤ) = 0
        ring
    by_cases hη : |η| ≤ δ / 2
    · have hset : (fareyWin Q θ δ).filter (fun x => JJ x = 0) = {x0} := by
        ext x; rw [Finset.mem_singleton, hfilt]; exact ⟨fun h => h.1, fun h => ⟨h, hη⟩⟩
      rw [hset, Finset.sum_singleton, spike, if_pos hη, mul_one]
      rfl
    · have hset : (fareyWin Q θ δ).filter (fun x => JJ x = 0) = ∅ := by
        ext x; rw [hfilt]; simp only [Finset.notMem_empty, iff_false, not_and]; intro _; exact hη
      rw [hset, Finset.sum_empty, spike, if_neg hη, mul_zero]
  · -- the lines
    have hR : ∑ j ∈ lineSet (lineM Q r η δ),
          ∑ k ∈ Finset.Icc ⌈((lineIv Q r j η δ).1 + r' * j) / (r : ℤ)⌉ ⌊((lineIv Q r j η δ).2 + r' * j) / (r : ℤ)⌋,
            (if Int.gcd k j = 1 then ZetaShell.OmegaW Q (F.omega Q) ((r : ℤ) * k - r' * j).toNat else 0)
        = ∑ p ∈ (lineSet (lineM Q r η δ)).sigma (fun j => (Finset.Icc ⌈((lineIv Q r j η δ).1 + r' * j) / (r : ℤ)⌉
              ⌊((lineIv Q r j η δ).2 + r' * j) / (r : ℤ)⌋).filter (fun k => Int.gcd k j = 1)),
            ZetaShell.OmegaW Q (F.omega Q) ((r : ℤ) * p.2 - r' * p.1).toNat := by
      rw [Finset.sum_sigma]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_filter]
    rw [hR]
    have hfwd : ∀ p ∈ (lineSet (lineM Q r η δ)).sigma (fun j => (Finset.Icc ⌈((lineIv Q r j η δ).1 + r' * j) / (r : ℤ)⌉
              ⌊((lineIv Q r j η δ).2 + r' * j) / (r : ℤ)⌋).filter (fun k => Int.gcd k j = 1)),
        (⟨((r : ℤ) * p.2 - r' * p.1).toNat, ((a * p.2 - a' * p.1) % ((r : ℤ) * p.2 - r' * p.1)).toNat⟩ :
            (_ : ℕ) × ℕ) ∈ fareyWin Q θ δ ∧
          BB ⟨((r : ℤ) * p.2 - r' * p.1).toNat, ((a * p.2 - a' * p.1) % ((r : ℤ) * p.2 - r' * p.1)).toNat⟩
            = a * p.2 - a' * p.1 ∧
          ((((r : ℤ) * p.2 - r' * p.1).toNat : ℕ) : ℤ) = (r : ℤ) * p.2 - r' * p.1 := by
      intro p hp
      obtain ⟨hpL, hpK⟩ := Finset.mem_sigma.mp hp
      obtain ⟨hpK1, hg⟩ := Finset.mem_filter.mp hpK
      have hpj : p.1 ≠ 0 := (Finset.mem_filter.mp hpL).2
      set q : ℤ := (r : ℤ) * p.2 - r' * p.1 with hqdef
      set B : ℤ := a * p.2 - a' * p.1 with hBdef
      set x : (_ : ℕ) × ℕ := ⟨q.toNat, (B % q).toNat⟩ with hxdef
      have hqb := lineK_bounds Q r hr r' p.1 η δ p.2 hpK1
      have hqpos : 0 < q := by omega
      have hqn : ((q.toNat : ℕ) : ℤ) = q := Int.toNat_of_nonneg (by omega)
      have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqb.1
      have hmemI := (mem_lineK (lineIv Q r p.1 η δ).1 (lineIv Q r p.1 η δ).2 r r' p.1 p.2
        (by exact_mod_cast hr)).mp hpK1
      have hline := (mem_lineIv Q r p.1 η δ (q : ℝ) hr hpj hqR).mp hmemI
      have hoff := line_offset a r a' r' hdet p.2 p.1 (by exact_mod_cast hqpos.ne') (by exact_mod_cast hr0.ne')
      have hgB : Int.gcd B q = 1 := by
        rw [hBdef, hqdef, line_gcd a r a' r' hdet p.2 p.1]; exact hg
      have hB0 : 0 ≤ B % q := Int.emod_nonneg B (by omega)
      have hBlt : B % q < q := Int.emod_lt_of_pos B hqpos
      have hBn : (((B % q).toNat : ℕ) : ℤ) = B % q := Int.toNat_of_nonneg hB0
      have hxI : x ∈ fareyIdx Q := by
        rw [mem_fareyIdx]
        show (1 ≤ q.toNat ∧ q.toNat ≤ Q) ∧ (B % q).toNat < q.toNat ∧ Nat.Coprime (B % q).toNat q.toNat
        refine ⟨⟨by omega, by omega⟩, by omega, ?_⟩
        rw [Nat.Coprime, ← Int.gcd_natCast_natCast, hBn, hqn, Int.gcd_emod]
        exact hgB
      have hptx : fareyPt x + ((B / q : ℤ) : ℝ) = (B : ℝ) / q := by
        have hd : (((B % q).toNat : ℕ) : ℝ) = (B : ℝ) - (q : ℝ) * ((B / q : ℤ) : ℝ) := by
          have : ((((B % q).toNat : ℕ) : ℤ) : ℝ) = ((B - q * (B / q) : ℤ) : ℝ) := by rw [hBn, Int.emod_def]
          push_cast at this ⊢; linarith
        have hqR' : ((q.toNat : ℕ) : ℝ) = (q : ℝ) := by exact_mod_cast hqn
        show ((((B % q).toNat : ℕ) : ℝ) / ((q.toNat : ℕ) : ℝ)) + ((B / q : ℤ) : ℝ) = (B : ℝ) / q
        rw [hd, hqR']
        have : (q : ℝ) ≠ 0 := by linarith
        field_simp
        ring
      have hclose : |fareyPt x + ((B / q : ℤ) : ℝ) - θ| ≤ δ / 2 := by
        rw [hptx, hθ]
        have e : (B : ℝ) / q - ((a : ℝ) / r + η) = (p.1 : ℝ) / ((q : ℝ) * r) - η := by
          have h' : (B : ℝ) / q - (a : ℝ) / r = (p.1 : ℝ) / ((q : ℝ) * r) := by
            have h'' := hoff
            push_cast at h'' ⊢
            rw [hBdef, hqdef]; push_cast; exact h''
          linarith
        rw [e, abs_le]
        constructor <;> linarith [hline.2.1, hline.2.2]
      have hwin : x ∈ fareyWin Q θ δ := hwin_of x hxI (B / q) hclose
      have hmmx : mm x = B / q := by
        have h1 := (hW x hwin).2
        rw [hBq x hxI] at h1
        exact int_eq_of_close (fareyPt x) θ δ hδ1 _ _ h1 hclose
      refine ⟨hwin, ?_, hqn⟩
      show ((x.2 : ℕ) : ℤ) + ((x.1 : ℕ) : ℤ) * mm x = B
      rw [hmmx]
      show (((B % q).toNat : ℕ) : ℤ) + ((q.toNat : ℕ) : ℤ) * (B / q) = B
      rw [hBn, hqn, Int.emod_def]; ring
    apply Finset.sum_nbij' (fun x => (⟨JJ x, KK x⟩ : (_ : ℤ) × ℤ))
      (fun p => (⟨((r : ℤ) * p.2 - r' * p.1).toNat, ((a * p.2 - a' * p.1) % ((r : ℤ) * p.2 - r' * p.1)).toNat⟩ :
        (_ : ℕ) × ℕ))
    · -- maps into the line set
      intro x hx'
      obtain ⟨hx, hj⟩ := Finset.mem_filter.mp hx'
      obtain ⟨hxI, hrep⟩ := hW x hx
      have hq1 : 1 ≤ x.1 := (mem_fareyIdx.mp hxI).1.1
      have hqQ : x.1 ≤ Q := (mem_fareyIdx.mp hxI).1.2
      have hq1R : (1 : ℝ) ≤ x.1 := by exact_mod_cast hq1
      have hqQR : (x.1 : ℝ) ≤ Q := by exact_mod_cast hqQ
      have hjq : (JJ x : ℝ) / ((x.1 : ℝ) * r) = (BB x : ℝ) / x.1 - θ + η := by
        rw [hθ]; simp only [hJJ]; push_cast; field_simp; ring
      rw [Finset.mem_sigma]
      constructor
      · unfold lineSet lineM
        rw [Finset.mem_filter, Finset.mem_Icc]
        refine ⟨?_, hj⟩
        have habs : |(JJ x : ℝ)| ≤ (r : ℝ) * Q * (|η| + δ / 2) := by
          have e : (JJ x : ℝ) = ((x.1 : ℝ) * r) * ((BB x : ℝ) / x.1 - θ + η) := by
            rw [← hjq]; field_simp
          rw [e, abs_mul, abs_of_pos (by positivity)]
          have h1 : |(BB x : ℝ) / x.1 - θ + η| ≤ δ / 2 + |η| := le_trans (abs_add_le _ _) (by linarith)
          calc (x.1 : ℝ) * r * |(BB x : ℝ) / x.1 - θ + η| ≤ (Q : ℝ) * r * (δ / 2 + |η|) := by
                apply mul_le_mul (mul_le_mul_of_nonneg_right hqQR hrR.le) h1 (abs_nonneg _) (by positivity)
            _ = (r : ℝ) * Q * (|η| + δ / 2) := by ring
        have hnat : (JJ x).natAbs ≤ ⌊(r : ℝ) * Q * (|η| + δ / 2)⌋₊ := by
          apply Nat.le_floor
          rw [Nat.cast_natAbs, Int.cast_abs]; exact habs
        have h2 : |JJ x| ≤ ((⌊(r : ℝ) * Q * (|η| + δ / 2)⌋₊ : ℕ) : ℤ) := by
          rw [← Int.natCast_natAbs]; exact_mod_cast hnat
        obtain ⟨h3, h4⟩ := abs_le.mp h2
        push_cast
        constructor <;> linarith
      · rw [Finset.mem_filter]
        constructor
        · rw [mem_lineK _ _ (r : ℤ) r' (JJ x) (KK x) (by exact_mod_cast hr), hq_of x]
          push_cast
          rw [mem_lineIv Q r (JJ x) η δ (x.1 : ℝ) hr hj hq1R]
          refine ⟨hqQR, ?_, ?_⟩ <;> rw [hjq] <;> linarith [(abs_le.mp hrep).1, (abs_le.mp hrep).2]
        · rw [← line_gcd a r a' r' hdet (KK x) (JJ x), hB_of x, hq_of x]
          exact Int.isCoprime_iff_gcd_eq_one.mp (hcopBq x hxI)
    · -- maps into the window, off the spike
      intro p hp
      obtain ⟨hwin, hBBx, hq⟩ := hfwd p hp
      rw [Finset.mem_filter]
      refine ⟨hwin, ?_⟩
      have hpj : p.1 ≠ 0 := (Finset.mem_filter.mp (Finset.mem_sigma.mp hp).1).2
      intro h0
      apply hpj
      have h1 : JJ ⟨((r : ℤ) * p.2 - r' * p.1).toNat, ((a * p.2 - a' * p.1) % ((r : ℤ) * p.2 - r' * p.1)).toNat⟩
          = p.1 := by
        simp only [hJJ]
        rw [hBBx, hq]
        linear_combination p.1 * hdet
      rw [← h1]; exact h0
    · -- left inverse
      intro x hx'
      obtain ⟨hx, _⟩ := Finset.mem_filter.mp hx'
      have hxI := (hW x hx).1
      have hx2lt : x.2 < x.1 := (mem_fareyIdx.mp hxI).2.1
      apply Sigma.ext
      · show ((r : ℤ) * KK x - r' * JJ x).toNat = x.1
        rw [hq_of x]; simp
      · apply heq_of_eq
        show ((a * KK x - a' * JJ x) % ((r : ℤ) * KK x - r' * JJ x)).toNat = x.2
        rw [hB_of x, hq_of x]
        simp only [hBB]
        rw [Int.add_mul_emod_self_left]
        have : (x.2 : ℤ) < (x.1 : ℤ) := by exact_mod_cast hx2lt
        rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) this]
        simp
    · -- right inverse
      intro p hp
      obtain ⟨_, hBBx, hq⟩ := hfwd p hp
      apply Sigma.ext
      · show BB _ * r - a * (((((r : ℤ) * p.2 - r' * p.1).toNat : ℕ)) : ℤ) = p.1
        rw [hBBx, hq]; linear_combination p.1 * hdet
      · apply heq_of_eq
        show r' * BB _ - a' * (((((r : ℤ) * p.2 - r' * p.1).toNat : ℕ)) : ℤ) = p.2
        rw [hBBx, hq]; linear_combination p.2 * hdet
    · -- the weights
      intro x _
      show ZetaShell.OmegaW Q (F.omega Q) x.1 = ZetaShell.OmegaW Q (F.omega Q) ((r : ℤ) * KK x - r' * JJ x).toNat
      rw [hq_of x]; simp

end TrackF
end ZetaShell
