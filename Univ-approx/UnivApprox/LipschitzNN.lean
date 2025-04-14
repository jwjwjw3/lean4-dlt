import UnivApprox.NeuralNetwork.SIGN
import UnivApprox.NeuralNetwork.ReLU
import UnivApprox.NeuralNetwork.NeuralNetwork
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Data.Real.Basic


------------------------------------------------------------------------
--------------- One dimentional Universal Approximation ----------------
noncomputable section

theorem finsum_diff_last (w:PNat) (m : ℕ) (f: (Fin w) → ℝ) (hmp1 : m+1 < w) (h : m < w) : f (m+1) =
    (∑ x ∈ Finset.filter (fun (x: Fin w) ↦ x ≤ (m+1)) Finset.univ, f (x) ) -
    (∑ x ∈ Finset.filter (fun (x: Fin w) ↦ x ≤ m) Finset.univ, f (x) ) := by
    rw [← Finset.sum_sdiff_sub_sum_sdiff]
    repeat rw [← @Finset.filter_and_not]
    have hm_N : m < m + 1 := by exact lt_add_one m
    have mp1_fin : (m + 1: Fin w) = ((m:ℕ) + 1 : ℕ) := by rw [@Nat.cast_add]; simp
    have mp1_fin' : ((m + 1: Fin w) : ℕ) = m + 1 := by rw [mp1_fin]; exact Fin.val_cast_of_lt hmp1
    have hm_fin : (m : Fin w) < (m+1 : Fin w) := by
      refine Fin.lt_def.mpr ?_
      rw [Fin.val_cast_of_lt h]
      exact Nat.lt_of_lt_of_eq hm_N (id (Eq.symm mp1_fin'))
    have hf1: ∀ (a : Fin w),
        a ∈ (Finset.univ : Finset (Fin w)) → ( (a ≤ m + 1 ∧ ¬a ≤ m) ↔ (a = m+1) ) := by
      intro a ha
      simp
      constructor
      · intro ⟨h1, h2⟩
        refine Fin.le_antisymm_iff.mpr ?_
        constructor
        · exact h1
        · contrapose h2
          rw [not_le] at h2
          rw [not_lt]
          rw [@Fin.le_iff_val_le_val]
          have h1_N : (a : ℕ) ≤ m + 1 := by exact le_of_le_of_eq h1 mp1_fin'
          have h2_N : (a : ℕ) < m + 1 := by exact Nat.lt_of_lt_of_eq h2 mp1_fin'
          have hm_N : ((m: Fin w) : ℕ) = m := by exact Fin.val_cast_of_lt h
          refine Nat.le_of_lt_succ ?_
          rw [Nat.succ_eq_add_one]
          exact Nat.lt_of_lt_of_eq h2_N (congrFun (congrArg HAdd.hAdd (id (Eq.symm hm_N))) 1)
      · intro hamp1
        constructor
        · exact Fin.ge_of_eq (id (Eq.symm hamp1))
        · rw [hamp1]
          exact hm_fin
    have hf2: ∀ (a : Fin w),
        a ∈ (Finset.univ : Finset (Fin w)) → ( (a ≤ m ∧ ¬a ≤ m + 1) ↔ false ) := by
      intro a ha
      simp
      intro ham
      calc
        a ≤ (m: Fin w) := by exact ham
        _ ≤ (m+1 : Fin w) := by exact Fin.le_of_lt hm_fin
    apply Finset.filter_inj'.mpr at hf1
    rw [hf1]
    apply Finset.filter_inj'.mpr at hf2
    rw [hf2]
    simp
    rw [@Finset.sum_filter]
    simp


theorem fin_last_iff (w : PNat) (k : Fin w) : k = Fin.last (w-1) ↔ (k : ℕ) = (w - 1 : ℕ) := by
  dsimp [Fin.last]
  constructor
  · rw [Nat.sub_one]
    intro h
    rw [h]
    refine Fin.val_cast_of_lt ?_
    refine Nat.pred_lt ?_
    exact PNat.ne_zero w
  · rw [Nat.sub_one]
    intro h
    rw [<-h]
    simp

def setB (w : PNat) (ε ρ : ℝ) (_ : Fin 1) (i : Fin w) : ℝ := i * (ε / ρ)

def setA (g : ℝ → ℝ) (w : PNat) (B : Matrix (Fin 1) (Fin w) ℝ)
    (_ : Fin 1) (i : Fin w) : ℝ :=
  if i = 0 then g 0 else (g (B 0 i) - g (B 0 (i-1)))

/-
Theorem:
  Suppose g : ℝ → ℝ is ρ-Lipschitz. For any ε > 0, there exists a 2-layer network f with ceil(ρ/ε)
  threshold nodes z ↦ 1[z ≥ 0] so that sup_{x∈[0,1]} |f(x)-g(x)| ≤ ε.
Proof idea:
  Define w := ceil(ρ/ε), bᵢ = i*(ε/ρ) ∀ i ∈ {0, 1, ..., m-1}, a₁ = g(0) and aᵢ = g(bᵢ) - g(bᵢ₋₁),
  and f(x) := ∑ aᵢ 1[xᵢ ≥ bᵢ]. ∀ x ∈ [0, 1], let k be the largest index so that bₖ ≤ x, then f is constant along [bₖ, x], and
  |g(x) - f(x)| ≤ |g(x) - g(bₖ)| + |g(bₖ) - f(bₖ)| + |f(bₖ) - f(x)|
                ≤ ρ |x - bₖ| + ∣g(bₖ) - ∑_{i=0}^{k} a| + 0
                ≤ ρ (ε/ρ) + ∣g(bₖ) - g(b₀) - ∑_{i=1}^{k} (g(bᵢ) - g(bᵢ₋₁)|
                = ε
-/

theorem univapprox_sign_nn_1d (ε ρ x : ℝ) (ep_pos : 0 < ε) (rho_pos : 0 < ρ)
    (S : Set ℝ) (S_def : S = {a| 0 ≤ a ∧ a ≤ 1 })(xs : x ∈ S)
    (w : PNat) (hw : w = Int.ceil (ρ / ε) )
    (g : ℝ → ℝ) (g_lipschitz : LipschitzOnWith (Real.toNNReal ρ) g S) :
    ∃ (A : Matrix (Fin 1) (Fin w) ℝ) (B : Matrix (Fin 1) (Fin w) ℝ),
      abs ( g x - NNsign2layer w A B x ) ≤ ε := by
  -- Get basic properties from constants
  have rho_div_rho_eq_one : ρ / ρ = 1 := by
    ring_nf; refine CommGroupWithZero.mul_inv_cancel ρ ?_ ; exact Ne.symm (ne_of_lt rho_pos)
  have eps_div_eps_eq_one : ε / ε = 1 := by
    ring_nf; refine CommGroupWithZero.mul_inv_cancel ε ?_ ; exact Ne.symm (ne_of_lt ep_pos)
  have rho_nonneg : 0 ≤ ρ := by exact le_of_lt rho_pos
  have ep_nonneg  : 0 ≤ ε := by exact le_of_lt ep_pos
  rw [S_def] at xs
  simp at xs
  -- Set A and B matrices
  set Bmat := Matrix.of (setB w ε ρ)
  set Amat := Matrix.of (setA g w Bmat)
  use Amat; use Bmat
  -- Set the largest index (k : Fin w) such that B 0 k ≤ x
  set Ks := {kᵢ | (Bmat 0 kᵢ) ≤ x}.toFinset
  have Ks_nonempty : Ks.Nonempty := by
    dsimp [Finset.Nonempty]
    use 0
    refine Set.mem_toFinset.mpr ?_
    simp [Bmat, setB]
    exact xs.1
  set k := Finset.max' Ks Ks_nonempty
  -- Get properties from k
  have Bk_le_x : Bmat 0 k ≤ x := by
    have k_in_Ks : k ∈ Ks := by exact Finset.max'_mem Ks Ks_nonempty
    simp [Ks] at k_in_Ks
    exact k_in_Ks
  have k_lt_w : (k : ℕ) < (w : ℕ) := by exact k.isLt
  have ksucc_le_w : (k:ℕ).succ ≤ (w:ℕ) := by exact k_lt_w
  have Bk_in_S : Bmat 0 k ∈ S := by
    rw [S_def]; simp [Bmat, setB]
    constructor
    · refine Right.mul_nonneg ?_ ?_
      exact Nat.cast_nonneg' ↑k
      exact div_nonneg ep_nonneg rho_nonneg
    · have ep_over_rho_pos : 0 < ε / ρ := by exact div_pos ep_pos rho_pos
      have ep_over_rho_nonneg : 0 ≤ ε / ρ := by exact le_of_lt ep_over_rho_pos
      have ceil_le_plus_one : ↑⌈ρ / ε⌉ < ρ / ε + 1 := by apply Int.ceil_lt_add_one (ρ / ε)
      have k_succ_le_w_R : ((k:ℕ).succ : ℝ) ≤ (w : ℝ) := by exact Nat.cast_le.mpr k_lt_w
      have kp1_le_w_R : (k+1: ℝ) ≤ (w : ℝ) := by simp at k_succ_le_w_R; exact k_succ_le_w_R
      have k_le_wn1_R : (k:ℝ) ≤ (w:ℝ) - 1 := by exact le_tsub_of_add_le_right kp1_le_w_R
      calc
        ↑↑k * (ε / ρ)
          ≤ (w-1) * (ε / ρ) := by exact mul_le_mul_of_nonneg_right k_le_wn1_R ep_over_rho_nonneg
        _ = (Int.ceil (ρ / ε)-1) * (ε / ρ) := by rw [<-hw]; rfl
        _ ≤ (ρ / ε) * (ε / ρ) := by
          refine mul_le_mul_of_nonneg_right ?_ ep_over_rho_nonneg
          refine tsub_le_iff_left.mpr ?_
          rw [add_comm]
          exact le_of_lt ceil_le_plus_one
        _ = (ρ / ρ) * (ε / ε) := by ring
        _ = 1 * (ε / ε) := by rw [div_self]; exact Ne.symm (ne_of_lt rho_pos)
        _ = 1 * 1       := by rw [div_self]; exact Ne.symm (ne_of_lt ep_pos)
        _ = 1 := by norm_num
  -- Prove necessary lemmas for the overall inequality calculations
  have h₁ : abs (g x - g (Bmat 0 k)) ≤ ρ * abs (x - Bmat 0 k) := by
    have h₁' : 0 ≤ ρ * dist x (Bmat 0 k) := by apply Right.mul_nonneg (le_of_lt rho_pos) dist_nonneg
    rw [<-Real.dist_eq (g x) (g (Bmat 0 k))]
    rw [<-Real.dist_eq x (Bmat 0 k)]
    refine (edist_le_ofReal ?_).mp ?_
    refine EReal.coe_nonneg.mp ?_
    exact EReal.coe_nonneg.mpr h₁'
    rw [ENNReal.ofReal_mul rho_nonneg]
    rw [<-edist_dist]
    simp [LipschitzOnWith] at g_lipschitz
    rw [S_def] at g_lipschitz
    apply g_lipschitz
    exact xs
    rw [S_def] at Bk_in_S
    exact Bk_in_S
  have h₂ : abs ( g (Bmat 0 k) - NNsign2layer w Amat Bmat (Bmat 0 k) ) =
      abs ( g (Bmat 0 k) - (∑ i : Fin w, if i ≤ k then (Amat 0 i) else 0) )  := by
    have ep_div_rho_pos : 0 < ε / ρ := by exact div_pos ep_pos rho_pos
    have h21 : ∀ (a : Fin w),
        a ∈ (Finset.univ : Finset (Fin w)) → ( (a * (ε / ρ) ≤ ↑↑k * (ε / ρ)) ↔ a ≤ ↑↑k) := by
      intro a ha
      constructor
      · intro hak
        have hak_R : (a : ℝ) ≤ (k : ℝ) := by exact le_of_mul_le_mul_right hak ep_div_rho_pos
        have hak_N: (a : ℕ) ≤ (k : ℕ) := by
          by_contra h21c1
          rw [not_le] at h21c1
          have not_hak_R : (k : ℝ) < (a : ℝ) := by exact Nat.cast_lt.mpr h21c1
          rw [<-not_le] at not_hak_R
          apply not_hak_R at hak_R
          exact hak_R
        exact hak_N
      · intro hak
        have hak_N : (a : ℕ) ≤ (k : ℕ) := by exact hak
        have hak_R : (a : ℝ) ≤ (k : ℝ) := by exact Nat.cast_le.mpr hak_N
        exact (mul_le_mul_iff_of_pos_right ep_div_rho_pos).mpr hak_R
    have h22 : NNsign2layer w Amat Bmat (Bmat 0 k) = ∑ i : Fin w, if i ≤ k then (Amat 0 i) else 0 := by
      simp [NNsign2layer, Bmat, sign_nonneg, setB]
      rw [Finset.sum_ite]
      rw [Finset.sum_ite]
      simp
      apply Finset.filter_inj'.mpr at h21
      rw [h21]
    exact congrArg abs (congrArg (HSub.hSub (g (Bmat 0 k))) h22)
  have h₃ : NNsign2layer w Amat Bmat (Bmat 0 k) - NNsign2layer w Amat Bmat x = 0 := by
    dsimp [NNsign2layer, sign_nonneg]
    simp
    rw [@sub_eq_zero]
    repeat rw [Finset.sum_ite]
    simp
    have h31 : ∀ (a : Fin w), a ∈ (Finset.univ : Finset (Fin w)) →
        ( (Bmat 0 a ≤ Bmat 0 k) ↔ (Bmat 0 a ≤ x)) := by
      intro a ha
      constructor
      · exact fun a_1 ↦ Preorder.le_trans (Bmat 0 a) (Bmat 0 k) x a_1 Bk_le_x
      · intro hax
        simp [Bmat, setB]
        have a_in_Ks : a ∈ Ks := by simp [Ks]; exact hax
        refine (mul_le_mul_right ?_).mpr ?_
        exact div_pos ep_pos rho_pos
        refine Nat.cast_le.mpr ?_
        refine Fin.val_le_of_le ?_
        exact Finset.le_max' Ks a a_in_Ks
    apply Finset.filter_inj'.mpr at h31
    rw [h31]
  have h₄ : abs (x - Bmat 0 k) ≤ ε / ρ := by
    apply sub_nonneg_of_le at Bk_le_x
    by_cases k_last : k = (Fin.last w) - 1
    · dsimp [Fin.last] at k_last
      have k_eq_w_sub_1 : (k:ℕ) = (w:ℕ)-1 := by
        rw [k_last]
        refine (fin_last_iff w (↑↑w - 1)).mp ?_
        simp
      have kp1_eq_w : (k:ℕ) + 1 = w := by
        refine Eq.symm (Nat.eq_add_of_sub_eq ?_ (id (Eq.symm k_eq_w_sub_1)))
        exact Nat.one_le_of_lt k_lt_w
      have k_succ_eq_w_N : (k : ℕ).succ = (w : ℕ) := by
        rw [Nat.succ_eq_add_one]; exact kp1_eq_w
      have k_succ_eq_w_R : (k : ℕ).succ = (w : ℝ) := by exact congrArg Nat.cast k_succ_eq_w_N
      have k_last_R : k = (w : ℝ) - 1 := by
        rw [Nat.succ_eq_add_one] at k_succ_eq_w_R; rw [<-k_succ_eq_w_R]; simp
      have Bk_val : Bmat 0 k = (w-1) * ε / ρ := by dsimp [Bmat, setB]; rw [k_last_R]; ring
      rw [abs_of_nonneg Bk_le_x]
      rw [Bk_val]
      ring_nf
      simp
      have hw_R : (w: ℝ) = Int.ceil (ρ / ε) := by
        exact Eq.symm (Real.ext_cauchy (congrArg Real.cauchy (congrArg Int.cast (id (Eq.symm hw)))))
      rw [hw_R]
      have h' : (ρ / ε) ≤ Int.ceil (ρ / ε) := by exact Int.le_ceil (ρ / ε)
      calc
        x ≤ 1 := by exact xs.2
        _ = (ρ / ρ) := by rw [<-rho_div_rho_eq_one]
        _ = (ρ / ρ) * 1 := by ring
        _ = (ρ / ρ) * (ε / ε) := by rw [<-eps_div_eps_eq_one]
        _ = (ρ / ε) * (ε * ρ⁻¹) := by ring
        _ ≤ Int.ceil (ρ / ε) * (ε * ρ⁻¹) := by
          refine (mul_le_mul_right ?_).mpr h'
          apply mul_pos ep_pos (inv_pos_of_pos rho_pos)
        _ = Int.ceil (ρ / ε) * ε * ρ⁻¹ := by ring
    · dsimp [Fin.last] at k_last
      have k_ne_w_sub_1_N : k ≠ (w - 1 : ℕ) := by
        contrapose k_last
        push_neg
        rw [Nat.sub_one] at k_last
        push_neg at k_last
        rw [k_last]
        refine Fin.eq_of_val_eq ?_
        simp
      by_contra h'
      rw [not_le] at h'
      rw [abs_of_nonneg Bk_le_x] at h'
      have kp1_ne_w : (k: ℕ).succ ≠ (w: ℕ) := by
        contrapose k_ne_w_sub_1_N
        push_neg
        push_neg at k_ne_w_sub_1_N
        rw [Nat.sub_one]
        rw [Nat.succ_eq_add_one] at k_ne_w_sub_1_N
        have k_eq_w_sub_1_N : (k : ℕ) = (w - 1 : ℕ) := by exact Nat.eq_sub_of_add_eq k_ne_w_sub_1_N
        rw [Nat.sub_one] at k_eq_w_sub_1_N
        refine Fin.eq_of_val_eq ?_
        rw [← k_eq_w_sub_1_N]
        simp
      have kp1_lt_w_N : (k: ℕ).succ < (w:ℕ) := by exact Nat.lt_of_le_of_ne k_lt_w kp1_ne_w
      have Bkp1_eq_ep_rho_p_Bk : Bmat 0 (k+1) = Bmat 0 k + ε / ρ := by
        simp [Bmat, setB]
        calc
          ↑↑(k + 1) * (ε / ρ)
            = (↑↑k+1)* (ε / ρ) := by
            have kp1_types : (((k+1 : ℕ) : Fin w) : ℕ) = (k+1: ℕ) := by
              rw [<-Nat.succ_eq_add_one]
              exact Fin.val_cast_of_lt kp1_lt_w_N
            have h_k_succ : (((k + 1) : Fin w) : ℕ) = (k : ℕ).succ := by
              rw [Nat.succ_eq_add_one]
              rw [<-kp1_types]
              simp
            have h_k_N : (((k + 1) : Fin w) : ℕ) = ( k + 1 : ℕ) := by exact h_k_succ
            have h_k_R : ((k + 1) : ℕ) = (k+1 : ℝ) := by exact Nat.cast_add_one ↑k
            rw [h_k_N, h_k_R]
          _ = ↑↑k * (ε / ρ) + (ε / ρ) := by exact add_one_mul (↑↑k) (ε / ρ)
      have Bkp1_le_x : Bmat 0 (k+1) ≤ x := by
        rw [Bkp1_eq_ep_rho_p_Bk]
        calc
          Bmat 0 k + ε / ρ = Bmat 0 k + (ε / ρ) := by ring
          _ ≤ Bmat 0 k + (x - Bmat 0 k) := by
            have h'' : ε / ρ ≤ x - Bmat 0 k := by exact le_of_lt h'
            exact (add_le_add_iff_left (Bmat 0 k)).mpr h''
          _ = x := by ring
      have kp1_in_Ks : (k+1) ∈ Ks := by dsimp [Ks]; simp; apply Bkp1_le_x
      have kp1_le_k : k + 1 ≤ k := by
        have k_max_of_Ks : ∀ k' ∈ Ks, k' ≤ k := by intro k'; exact fun a ↦ Finset.le_max' Ks k' a
        exact k_max_of_Ks (k + 1) kp1_in_Ks
      have kp1_gt_k : k < k + 1 := by
        refine Fin.lt_def.mpr ?_
        have kp1_fin : (k + 1: Fin w) = ((k:ℕ) + 1 : ℕ) := by
          rw [Nat.succ_eq_add_one] at kp1_lt_w_N
          rw [@Nat.cast_add]
          simp
        have kp1_fin_N : ((k + 1: Fin w): ℕ) = ((k:ℕ) + 1 : ℕ) := by rw [kp1_fin]; exact Fin.val_cast_of_lt kp1_lt_w_N
        rw [kp1_fin_N]
        linarith
      rw [<-not_le] at kp1_gt_k
      apply kp1_gt_k at kp1_le_k
      exact kp1_le_k
  have h₅ : abs ( g (Bmat 0 k) - (∑ i : Fin w, if i ≤ k then (Amat 0 i) else 0) ) = 0 := by
    have w_pos: 0 < (w:ℕ) := by exact PNat.pos w
    rw [abs_eq_zero]
    simp [Amat, Bmat, setB, setA, setB]
    rw [@sub_eq_zero]
    rw [@Finset.sum_ite]
    simp
    have h51: ∀ (m : Fin w), g (m * (ε / ρ)) =
        ∑ x ∈ Finset.filter (fun x ↦ x ≤ m) Finset.univ, if x = 0 then g 0 else g (↑↑x * (ε / ρ)) - g (↑↑(x - 1) * (ε / ρ)) := by
      intro m
      induction' m with Nm Hm
      induction' Nm with m' ih
      · simp
        have h52 : ∀ (a : Fin w),
            a ∈ Finset.univ → ((fun x ↦ x ≤ @Fin.mk (↑w) 0 Hm ) a ↔ a = 0) := by
          intro a ha
          constructor
          · simp
            intro hfa
            exact Fin.le_zero_iff'.mp hfa
          · simp
            intro hfa
            rw [hfa]
            simp
        apply Finset.filter_inj'.mpr at h52
        rw [h52]
        have h53 : Finset.filter (fun (a : (Fin w)) ↦ a = 0) Finset.univ = {0} := by
          refine Finset.eq_singleton_iff_unique_mem.mpr ?_; simp
        rw [h53]
        simp
      · have Hm' : m' < w := by exact Nat.lt_of_succ_lt Hm
        have h54 : g ((@Fin.mk (↑w) (m') Hm') * (ε / ρ)) =
            ∑ x ∈ Finset.filter (fun x ↦ x ≤ (@Fin.mk (↑w) (m') Hm')) Finset.univ,
              if x = 0 then g 0 else g (↑↑x * (ε / ρ)) - g (↑↑(x - 1) * (ε / ρ)) := by rw [← ih]
        rw [@Finset.sum_filter]
        have h55 : g ((@Fin.mk (↑w) (m'+1) Hm) * (ε / ρ)) - g ((@Fin.mk (↑w) (m') Hm') * (ε / ρ)) =
            ( ∑ a : Fin ↑w, if a ≤ ⟨m' + 1, Hm⟩ then if a = 0 then g 0 else g (↑↑a * (ε / ρ)) - g (↑↑(a - 1) * (ε / ρ)) else 0 ) -
            ( ∑ x ∈ Finset.filter (fun x ↦ x ≤ (@Fin.mk (↑w) (m') Hm')) Finset.univ, if x = 0 then g 0 else g (↑↑x * (ε / ρ)) - g (↑↑(x - 1) * (ε / ρ)) ) := by
          rw [<-@Finset.sum_filter]
          have castm': (@Fin.mk (↑w) (m') Hm') = m' := by
            refine Fin.eq_of_val_eq ?_
            exact Eq.symm (Fin.val_cast_of_lt Hm')
          have castmp1': (@Fin.mk (↑w) (m'+1) Hm) = m'+1 := by
            refine Fin.eq_of_val_eq ?_
            rw [← @Nat.cast_succ]
            rw [Fin.val_cast_of_lt Hm]
          rw [castm', castmp1']
          rw [<-finsum_diff_last w m' (fun a ↦ if a = 0 then g 0 else g (↑↑a * (ε / ρ)) - g (↑↑(a - 1) * (ε / ρ))) Hm Hm']
          have mp1ne0 : (m' + 1 : Fin w) ≠ 0 := by
            have mp1_N : (m' + 1 : Fin w) = (m' + 1 : ℕ) := by simp
            rw [<-Nat.succ_eq_add_one] at Hm
            rw [mp1_N]
            rw [@Fin.ne_iff_vne]
            rw [Fin.val_zero']
            rw [Fin.val_cast_of_lt Hm]
            simp
          rw [@eq_ite_iff]
          right
          constructor
          · exact mp1ne0
          · rw [@add_sub_assoc]
            rw [@Fin.sub_self]
            rw [@Fin.add_zero]
        rw [h54] at h55
        simp at h55
        rw [<-h55]
        simp
    exact h51 k
  -- Perform overall inequality calculations
  calc abs (g x - NNsign2layer w Amat Bmat x)
      ≤ abs (g x - g (Bmat 0 k)) + abs (g (Bmat 0 k) - NNsign2layer w Amat Bmat x) := by
        exact abs_sub_le (g x) (g (Bmat 0 k)) (NNsign2layer w Amat Bmat x)
    _ ≤ abs (g x - g (Bmat 0 k)) + ( abs (g (Bmat 0 k) - NNsign2layer w Amat Bmat (Bmat 0 k))
          + abs (NNsign2layer w Amat Bmat (Bmat 0 k) - NNsign2layer w Amat Bmat x) ) := by
        have hNN : abs (g (Bmat 0 k) - NNsign2layer w Amat Bmat x)
            ≤ abs (g (Bmat 0 k) - NNsign2layer w Amat Bmat (Bmat 0 k))
              + abs (NNsign2layer w Amat Bmat (Bmat 0 k) - NNsign2layer w Amat Bmat x) := by
          exact abs_sub_le (g (Bmat 0 k)) (NNsign2layer w Amat Bmat (Bmat 0 k)) (NNsign2layer w Amat Bmat x)
        exact (add_le_add_iff_left |g x - g (Bmat 0 k)|).mpr hNN
    _ ≤ ρ * abs (x - Bmat 0 k) + ( abs (g (Bmat 0 k) - NNsign2layer w Amat Bmat (Bmat 0 k))
          + abs (NNsign2layer w Amat Bmat (Bmat 0 k) - NNsign2layer w Amat Bmat x) ) := by
        exact add_le_add_right h₁
            ( |g (Bmat 0 k) - NNsign2layer w Amat Bmat (Bmat 0 k)|
             + |NNsign2layer w Amat Bmat (Bmat 0 k) - NNsign2layer w Amat Bmat x| )
    _ ≤ ρ * (ε / ρ) + ( abs (g (Bmat 0 k) - NNsign2layer w Amat Bmat (Bmat 0 k))
          + abs (NNsign2layer w Amat Bmat (Bmat 0 k) - NNsign2layer w Amat Bmat x) ) := by
        refine (add_le_add_iff_right
                (|g (Bmat 0 k) - NNsign2layer w Amat Bmat (Bmat 0 k)| +
                  |NNsign2layer w Amat Bmat (Bmat 0 k) - NNsign2layer w Amat Bmat x|)).mpr ?_
        exact (mul_le_mul_iff_of_pos_left rho_pos).mpr h₄
    _ ≤ ρ * (ε / ρ) + ( abs (g (Bmat 0 k) - (∑ i : Fin w, if i ≤ k then (Amat 0 i) else 0))
          + abs (NNsign2layer w Amat Bmat (Bmat 0 k) - NNsign2layer w Amat Bmat x) ) := by
        exact le_of_eq
            (congrArg (HAdd.hAdd (ρ * (ε / ρ)))
              (congrFun (congrArg HAdd.hAdd h₂)
                |NNsign2layer w Amat Bmat (Bmat 0 k) - NNsign2layer w Amat Bmat x|))
    _ = ρ * (ε / ρ) + abs (g (Bmat 0 k) - (∑ i : Fin w, if i ≤ k then (Amat 0 i) else 0) ) + 0 := by rw [h₃]; norm_num
    _ = ρ * (ε / ρ) + 0 + 0 := by exact congrFun (congrArg HAdd.hAdd (congrArg (HAdd.hAdd (ρ * (ε / ρ))) h₅)) 0
    _ = ρ * (ε / ρ) + 0 := by exact AddMonoid.add_zero (ρ * (ε / ρ) + 0)
    _ = ρ * (ε / ρ)     := by exact AddMonoid.add_zero (ρ * (ε / ρ))
    _ = (ρ / ρ) * ε := by ring
    _ = 1 * ε := by rw [rho_div_rho_eq_one]
    _ = ε := by norm_num

end

------------------------------------------------------------------------
