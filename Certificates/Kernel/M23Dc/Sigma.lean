module

public import Certificates.Kernel.M23Dc.Final
public import Certificates.Kernel.M23Dc.InclChecks
public import Certificates.Kernel.M23Dc.SigmaC4
public import Certificates.Kernel.M23Dc.SigmaC6
public import CFSG.Certificates.Kernel.SporLatSigmaLSound
public import CFSG.Certificates.Kernel.E64LEq
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatIncl

public section

namespace CFSG.KD.M23Dc

open CFSG.KC.SLDc CFSG.KC.SLSig CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Quasithin.H.MathieuLat

theorem m23LatS_eq : m23LatS = m23LatK := by
  unfold m23LatS m23LatK
  rw [T_eq.1, T_eq.2.1, T_eq.2.2]
  simp

theorem gK_iff {j jj : ℕ} (hj : j < 16) (hjj : jj < 16) :
    GensIn (codeSetAct 23) m23Delta m23LatK j jj ↔ gK j jj = true := by
  rw [codeSetAct_eq, delta_eq]
  unfold gK
  apply gensIn_iff_gensInL
  · rw [mt_get hj, mw_get, wordTabA_eq_L, ← T_eq.1, ← T_eq.2.1]
  · rw [Om_get hjj]
    rfl

theorem incl_getD (j : ℕ) : m23Incl[j]! = m23Incl.getD j [] := by
  simp only [List.getElem!_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  rfl

theorem m23K_gensIn_iff : ∀ j < 16, ∀ jj < 16,
    (GensIn (codeSetAct 23) m23Delta m23LatK j jj ↔ jj ∈ m23Incl[j]!) := by
  intro j hj jj hjj
  have h := List.all_eq_true.1 (List.all_eq_true.1 inclB j (List.mem_range.2 hj)) jj
    (List.mem_range.2 hjj)
  rw [beq_iff_eq] at h
  rw [gK_iff hj hjj, h, List.contains_iff_mem, incl_getD]


theorem m23K_Y_le_iff {j jj : ℕ} (hj : j < 16) (hjj : jj < 16) :
    m23CtxK.Y j ≤ m23CtxK.Y jj ↔ jj ∈ m23Incl[j]! := by
  rw [m23CtxK.Y_le_iff (by rw [m23K_J]; exact hj) (by rw [m23K_J]; exact hjj)]
  exact m23K_gensIn_iff j hj jj hjj

theorem sigK_ctx {j : ℕ} (h : sigK j = true) :
    sigmaCheckL (CFSG.KC.E64L.codeSetTL 23) 23 m23CtxK.Δ m23CtxK.D lblK [j]
      [4, 6, 10, 11, 12, 13, 14] = true := by
  change sigmaCheckL (CFSG.KC.E64L.codeSetTL 23) 23 m23Delta m23LatK lblK [j]
    [4, 6, 10, 11, 12, 13, 14] = true
  rw [delta_eq, ← m23LatS_eq]
  exact h

theorem m23K_sigma_test :
    ∀ j ∈ ({4, 6} : Finset ℕ), ∀ k ∈ ({4, 6, 10, 11, 12, 13, 14} : Finset ℕ),
      ∀ e x σ : G, e ∈ m23CtxK.Y j → orderOf e = 3 → x ∈ m23CtxK.Y k → x ∉ m23CtxK.Y j →
        orderOf x = 3 → e * x = x * e → σ ∈ m23CtxK.S → σ * e * σ⁻¹ = e⁻¹ →
        σ * x * σ⁻¹ = x → False := by
  intro j hj k hk
  have hj' : j = 4 ∨ j = 6 := by simpa using hj
  have hj16 : j < 16 := by omega
  have hsig : sigK j = true := by
    rcases hj' with rfl | rfl
    · exact sig4
    · exact sig6
  have hact : ∀ g : G, CFSG.KC.E64L.codeSetTL 23 (tab 23 g) m23CtxK.Δ =
      lab 23 m23CtxK.A m23CtxK.Δ g := by
    intro g
    change _ = codeSetAct 23 (tab 23 g).toArray m23Delta
    rw [codeSetAct_eq, CFSG.KC.E64L.codeSetT_eqT]
    rfl
  refine sigmaCheckL_sound m23CtxK (js := [j]) (ks := [4, 6, 10, 11, 12, 13, 14])
    (fun j' hj' => ?_) (fun k' hk' => ?_) hact (fun j' hj' => ?_) (sigK_ctx hsig) j
    (List.mem_singleton_self j) k (by simpa using hk)
  · rw [List.mem_singleton.1 hj', m23K_J]
    exact hj16
  · rw [m23K_J]
    simp at hk'
    omega
  · rw [List.mem_singleton.1 hj', m23K_D_Om, Om_get hj16]
    rfl

end CFSG.KD.M23Dc

end
