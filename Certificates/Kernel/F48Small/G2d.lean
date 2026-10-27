module

public import CFSG.Milestones.ASVolI.F48.Small.G2dInputs
public import Certificates.Data.Kernel.F48Small.G2dK
public import Certificates.Kernel.SporSch.Th.GenStr
public import Certificates.Kernel.StdOdd.ValsCmd

public section

set_option maxRecDepth 100000 in
#kss_strof CertificateChecks.KernelF48S.G2dTab CFSG.ASVolI.burnsideF48s_g2dTab

namespace CertificateChecks.KernelF48S

open CFSG.ASVolI CFSG.KC.F48S CFSG.KC.LQT.L CFSG.KC.Ord CFSG.Quasithin

@[expose] noncomputable def ekG2d (w : List (Fin 5 × Bool)) : ℕ :=
  evK 28 (burnsideF48s_g2dGL.map encL) (burnsideF48s_g2dGLi.map encL) w

@[expose] noncomputable def g2dFT (k : ℕ) : ℕ := ekG2d (burnsideF48s_g2dTelF k)

@[expose] noncomputable def g2dFTi (k : ℕ) : ℕ :=
  ekG2d (burnsideF48s_invW (burnsideF48s_g2dTelF k))

@[expose] noncomputable def g2dFA (k : ℕ) : ℕ := ekG2d (burnsideF48s_g2dAF k)

@[expose] noncomputable def g2dFB (k : ℕ) : ℕ := ekG2d (burnsideF48s_g2dBF k)

@[expose] noncomputable def g2dFV (k : ℕ) : ℕ :=
  ekG2d (u33Word (burnsideF48s_g2dCandV.getD k ""))

@[expose] noncomputable def g2dFW (k : ℕ) : ℕ := ekG2d (u33Word (["Xs", "Y", "X"].getD k ""))

#kc_vals G2dT g2dFT 32
#kc_vals G2dTi g2dFTi 32
#kc_vals G2dA g2dFA 64
#kc_vals G2dA8 g2dFA 8
#kc_vals G2dB g2dFB 64
#kc_vals G2dV g2dFV 4
#kc_vals G2dW g2dFW 3

@[expose] noncomputable def g2dId : ℕ := encL (List.range 28)

@[expose] noncomputable def g2dTri : List (ℕ × ℕ × ℕ) :=
  triK burnsideF48s_g2dDig G2dTab.chars 0 0 0

@[expose] noncomputable def g2dCandP : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Bool :=
  candAt G2dT.V G2dTi.V G2dA.V G2dB.V G2dV.V (getK G2dW.V 0) (getK G2dW.V 1)

theorem g2d_chars_length : G2dTab.chars.length = 12288 := by decide +kernel

set_option maxRecDepth 100000 in
theorem g2d_cand0 : walkC g2dCandP 0 g2dTri 0 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem g2d_cand1 : walkC g2dCandP 1 g2dTri 0 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem g2d_cand2 : walkC g2dCandP 2 g2dTri 0 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem g2d_cand3 : walkC g2dCandP 3 g2dTri 0 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem g2d_cand4 : walkC g2dCandP 4 g2dTri 0 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem g2d_cand5 : walkC g2dCandP 5 g2dTri 0 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem g2d_cand6 : walkC g2dCandP 6 g2dTri 0 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem g2d_cand7 : walkC g2dCandP 7 g2dTri 0 = true := by decide +kernel

@[expose] noncomputable def g2dCheckATw (L : List ℕ) : Bool :=
  allA G2dT.V fun t₁ => allA G2dT.V fun t₂ =>
    orB (notB (Nat.beq (pcomp (pcomp (pcomp t₁ 28 (getK G2dW.V 2)) 28 t₂) 28
        (pcomp (pcomp t₁ 28 (getK G2dW.V 2)) 28 t₂)) g2dId))
      (anyA L fun x => Nat.beq (pcomp (pcomp t₁ 28 (getK G2dW.V 2)) 28 t₂) x)

@[expose] noncomputable def g2dCheckBTw (L : List ℕ) : Bool :=
  allA G2dT.V fun t₁ => allA G2dT.V fun t₂ =>
    anyA L fun x => Nat.beq (pcomp (pcomp t₁ 28 (getK G2dW.V 1)) 28 t₂) x

theorem g2d_checkA : g2dCheckATw G2dA8.V = true := by decide +kernel

theorem g2d_checkB : g2dCheckBTw G2dB.V = true := by decide +kernel

theorem g2d_rel1 : Nat.beq (ekG2d (burnsideF48s_g2dCand 1)) g2dId = true := by decide +kernel

theorem g2d_rel3 : Nat.beq (ekG2d (burnsideF48s_g2dCand 3)) g2dId = true := by decide +kernel

theorem g2d_gens : burnsideF48s_g2dCheckGens () = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem g2d_negCandUY :
    notB (walkC (candAt G2dT.V G2dTi.V G2dA.V G2dB.V G2dV.V (getK G2dW.V 1) (getK G2dW.V 0)) 0
      g2dTri 0) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem g2d_negCandTab :
    notB (walkC g2dCandP 0 (triK burnsideF48s_g2dDig ('1' :: G2dTab.chars) 0 0 0) 0) = true := by
  decide +kernel

theorem g2d_negA : notB (g2dCheckATw G2dA8.V.tail) = true := by decide +kernel

theorem g2d_negB : notB (g2dCheckBTw G2dB.V.tail) = true := by decide +kernel

theorem g2d_negRel0 : notB (Nat.beq (ekG2d (burnsideF48s_g2dCand 0)) g2dId) = true := by
  decide +kernel

end CertificateChecks.KernelF48S
