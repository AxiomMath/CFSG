module

public import CFSG.Milestones.ASVolI.F48.Small.G2dInputs
public import Certificates.Data.Kernel.F48Small.G2dConj
public import Certificates.Data.Kernel.F48Small.G2dK
public import Certificates.Data.Kernel.F48Small.G2dVals
public import Certificates.Data.Kernel.Misc.E6Std
public import Certificates.Kernel.SporSch.Th.GenStr

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

open CFSG.KC.Misc.E6Std (nthV) in
theorem G2dT.all : ∀ k < 32, Nat.beq (g2dFT k) (nthV G2dT.V k) = true := by decide +kernel
open CFSG.KC.Misc.E6Std (nthV) in
theorem G2dTi.all : ∀ k < 32, Nat.beq (g2dFTi k) (nthV G2dTi.V k) = true := by decide +kernel
open CFSG.KC.Misc.E6Std (nthV) in
theorem G2dA.all : ∀ k < 64, Nat.beq (g2dFA k) (nthV G2dA.V k) = true := by decide +kernel
open CFSG.KC.Misc.E6Std (nthV) in
theorem G2dA8.all : ∀ k < 8, Nat.beq (g2dFA k) (nthV G2dA8.V k) = true := by decide +kernel
open CFSG.KC.Misc.E6Std (nthV) in
theorem G2dB.all : ∀ k < 64, Nat.beq (g2dFB k) (nthV G2dB.V k) = true := by decide +kernel
open CFSG.KC.Misc.E6Std (nthV) in
theorem G2dV.all : ∀ k < 4, Nat.beq (g2dFV k) (nthV G2dV.V k) = true := by decide +kernel
open CFSG.KC.Misc.E6Std (nthV) in
theorem G2dW.all : ∀ k < 3, Nat.beq (g2dFW k) (nthV G2dW.V k) = true := by decide +kernel

@[expose] noncomputable def g2dId : ℕ := encL (List.range 28)

@[expose] noncomputable def g2dTri : List (ℕ × ℕ × ℕ) :=
  triK burnsideF48s_g2dDig G2dTab.chars 0 0 0

theorem G2dCA.all : ∀ t < 32, ∀ a < 8, Nat.beq (getK (getKL G2dCA.V t) a)
    (pcomp (pcomp (getK G2dT.V t) 28 (getK G2dA.V a)) 28 (getK G2dTi.V t)) = true := by
  decide +kernel

theorem G2dCB.all : ∀ t < 32, ∀ b < 64, Nat.beq (getK (getKL G2dCB.V t) b)
    (pcomp (pcomp (getK G2dT.V t) 28 (getK G2dB.V b)) 28 (getK G2dTi.V t)) = true := by
  decide +kernel

theorem G2dYR.all : ∀ r < 32, Nat.beq (pcomp (getK G2dYR.V r) 28 (getK G2dT.V r))
    (getK G2dW.V 1) = true := by
  decide +kernel

theorem G2dVr.all : ∀ r < 32, ∀ j < 4, Nat.beq
    (pcomp (pcomp (getK G2dTi.V r) 28 (getK (getKL G2dVr.V r) j)) 28 (getK G2dT.V r))
    (getK G2dV.V j) = true := by
  decide +kernel

@[expose] noncomputable def g2dCandP : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Bool :=
  candAt G2dCA.V G2dCB.V G2dVr.V G2dYR.V (getK G2dW.V 0)

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
    notB (walkC (candAt G2dCA.V G2dCB.V G2dVr.V G2dYR.V (getK G2dW.V 1)) 0 g2dTri 0) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem g2d_negCandTab :
    notB (walkC g2dCandP 0 (triK burnsideF48s_g2dDig ('1' :: G2dTab.chars) 0 0 0) 0) = true := by
  decide +kernel

theorem g2d_negA : notB (g2dCheckATw G2dA8.V.tail) = true := by decide +kernel

theorem g2d_negB : notB (g2dCheckBTw G2dB.V.tail) = true := by decide +kernel

theorem g2d_negRel0 : notB (Nat.beq (ekG2d (burnsideF48s_g2dCand 0)) g2dId) = true := by
  decide +kernel

end CertificateChecks.KernelF48S
