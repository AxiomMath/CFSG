module

public import Certificates.Kernel.KGC31M24.Defs7217
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.KGC31M24.Data7217
public import CFSG.Certificates.Kernel.KGC31PLazy
public import CFSG.Certificates.Kernel.KGC31PNormGen

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelKGC31M24

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.KGC31P
open CFSG.Quasithin.KGC31.M24 CertificateChecks.KernelSporSch

theorem kLq : Nat.beq (pcountProducts 24 5 (pcommAll 24 5 u5P) (trPL 24 5 CLQ.LR CLQ.TR 5)
    (pidn 24 5)) 64 = true := by quickRfl

@[expose] def lsB : List Nat := [0, 1, 2, 3, 4]

@[expose] def lsC : List (List Nat) :=
  [[0, 4, 17, 20], [1, 10, 21, 22], [2, 3, 8, 13], [2, 3, 8, 13], [0, 4, 17, 20]]

theorem kLsFix : (List.range 5).all (fun j => ((trPL 24 5 CLS.LR CLS.TR 5).getD j []).all fun t =>
    (List.range j).all fun i => Nat.beq (pg 5 (mask 5) t (lsB.getD i 0)) (lsB.getD i 0)) = true := by
  quickRfl

theorem kLs : Nat.beq (pcountProducts 24 5 (pfixesBlocks 5 tets) (trPL 24 5 CLS.LR CLS.TR 5)
    (pidn 24 5)) 192 = true := by
  have hlen : (trPL 24 5 CLS.LR CLS.TR 5).length = 5 := by simp [trPL]
  have hmem : ∀ i < 5, lsC.getD i [] ∈ tets ∧ lsB.getD i 0 ∈ lsC.getD i [] := by decide
  have hfix := kLsFix
  rw [pcount_pr (B := lsB) (C := lsC) (by decide) _ 0
    (fun i hi => by rw [hlen] at hi; rw [Nat.zero_add]; revert i; decide)
    (fun j hj t ht i hi => by
      rw [hlen] at hj
      rw [Nat.zero_add]
      have h := List.all_eq_true.1 (List.all_eq_true.1 (List.all_eq_true.1 hfix j
        (List.mem_range.2 hj)) t ht) i (List.mem_range.2 hi)
      exact Nat.eq_of_beq_eq_true h)
    (fun x hx i hi => by
      rw [hlen] at hi
      rw [Nat.zero_add]
      exact pfixes_contains (hmem i hi).1 (hmem i hi).2 hx)]
  quickRfl

@[expose] noncomputable def cb0TL : List (List Nat) := trPL 24 5 M24C2.LR M24C2.TR 4

theorem cb0_countP (gs : List Nat) :
    cb0P.countP (pcommAll 24 5 gs) = pcountL 24 5 (pcommL 24 5 gs) cb0TL (pidn 24 5) :=
  countP_all_eq_L (fun g t => pcommL_eq (by decide) (by decide) gs g t)
    (trPL 24 5 M24C2.LR M24C2.TR 4) (pidn 24 5)
    (by unfold trPL; exact List.ne_nil_of_length_pos (by simp))

theorem kC2L_oP : Nat.beq (pcountL 24 5 (pcommL 24 5 oP) cb0TL (pidn 24 5)) 16 = true := by
  quickRfl

theorem kC2L_sP : Nat.beq (pcountL 24 5 (pcommL 24 5 sP) cb0TL (pidn 24 5)) 64 = true := by
  quickRfl

theorem kC2L_s16P : Nat.beq (pcountL 24 5 (pcommL 24 5 s16P) cb0TL (pidn 24 5)) 64 = true := by
  quickRfl

theorem kC2L_s32P : Nat.beq (pcountL 24 5 (pcommL 24 5 s32P) cb0TL (pidn 24 5)) 64 = true := by
  quickRfl

theorem kC2L_r2P : Nat.beq (pcountL 24 5 (pcommL 24 5 r2P) cb0TL (pidn 24 5)) 16 = true := by
  quickRfl

theorem kC2L_u4P : Nat.beq (pcountL 24 5 (pcommL 24 5 u4P) cb0TL (pidn 24 5)) 16 = true := by
  quickRfl

theorem kC2L_u5P : Nat.beq (pcountL 24 5 (pcommL 24 5 u5P) cb0TL (pidn 24 5)) 128 = true := by
  quickRfl

theorem kC2L_tP : Nat.beq (pcountL 24 5 (pcommL 24 5 tP) cb0TL (pidn 24 5)) 64 = true := by
  quickRfl

theorem kC2L : (Nat.beq (pcountL 24 5 (pcommL 24 5 oP) cb0TL (pidn 24 5)) 16 &&
    Nat.beq (pcountL 24 5 (pcommL 24 5 sP) cb0TL (pidn 24 5)) 64 &&
    Nat.beq (pcountL 24 5 (pcommL 24 5 s16P) cb0TL (pidn 24 5)) 64 &&
    Nat.beq (pcountL 24 5 (pcommL 24 5 s32P) cb0TL (pidn 24 5)) 64 &&
    Nat.beq (pcountL 24 5 (pcommL 24 5 r2P) cb0TL (pidn 24 5)) 16 &&
    Nat.beq (pcountL 24 5 (pcommL 24 5 u4P) cb0TL (pidn 24 5)) 16 &&
    Nat.beq (pcountL 24 5 (pcommL 24 5 u5P) cb0TL (pidn 24 5)) 128 &&
    Nat.beq (pcountL 24 5 (pcommL 24 5 tP) cb0TL (pidn 24 5)) 64) = true := by
  rw [kC2L_oP, kC2L_sP, kC2L_s16P, kC2L_s32P, kC2L_r2P, kC2L_u4P, kC2L_u5P, kC2L_tP]
  rfl

theorem kC2 : (Nat.beq (cb0P.countP (pcommAll 24 5 oP)) 16 &&
    Nat.beq (cb0P.countP (pcommAll 24 5 sP)) 64 &&
    Nat.beq (cb0P.countP (pcommAll 24 5 s16P)) 64 &&
    Nat.beq (cb0P.countP (pcommAll 24 5 s32P)) 64 &&
    Nat.beq (cb0P.countP (pcommAll 24 5 r2P)) 16 &&
    Nat.beq (cb0P.countP (pcommAll 24 5 u4P)) 16 &&
    Nat.beq (cb0P.countP (pcommAll 24 5 u5P)) 128 &&
    Nat.beq (cb0P.countP (pcommAll 24 5 tP)) 64) = true := by
  simp only [cb0_countP]
  exact kC2L

theorem kC1 : Nat.beq (cb1P.countP (pcommAll 24 5 u6P)) 64 = true := by quickRfl

end CertificateChecks.KernelKGC31M24

end
