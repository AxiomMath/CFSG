module

public import Certificates.Kernel.E68Spor4215.D
public import Certificates.Kernel.LocalQT.Base.C4141D
public import Certificates.Data.Kernel.SporLatOm
public import Certificates.Data.Kernel.LocalQT.PermW
public import Certificates.Data.E68Spor.Words
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHeCertificateInputs
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.E68S4215.He

open CFSG.KC.SLOm CFSG.Quasithin.E6.Spor CFSG.QuasithinUnique.Ch1.SporLat.He

@[expose] noncomputable def cL : List Nat :=
  [CFSG.KD.LQT.C4141.TF 197, CFSG.KD.LQT.C4141.TF 207, CFSG.KD.LQT.C4141.TF 226,
    CFSG.KD.LQT.C4141.TF 247, TF 0]

@[expose] noncomputable def L (l p : Nat) : Nat := CFSG.KC.LQT.PW.imgW 14 (cL.getD l 0) p

@[expose] noncomputable def AB (l p : Nat) : Nat :=
  CFSG.KC.LQT.PW.imgW 14 (CFSG.KD.LQT.C4141.TF l) p

@[expose] noncomputable def Z (p : Nat) : Nat := CFSG.KC.LQT.PW.imgW 14 (CFSG.KD.LQT.C4141.TF 170) p

@[expose] def rWordsF (n : Nat) (L : Nat → Nat → Nat) (ns : Nat) (AB : Nat → Nat → Nat)
    (uWords : List (List Nat)) : Bool :=
  (List.range uWords.length).all (fun k => (List.range n).all fun p =>
    L (ns + k) p ==
      CFSG.KC.E64F.wordF AB (uWords.getD k []) p)

@[expose] def rRestF (n : Nat) (Δ : List Nat) (L : Nat → Nat → Nat) (ns : Nat) (z : Nat → Nat)
    (uWords : List (List Nat)) (yw nw : List Nat) (r m fuel : Nat) : Bool :=
  open CFSG.KC.E64F CFSG.KC.SLOm in
  uWords.all (fun w => w.all fun l => decide (l < 2)) &&
    yw.all (fun l => decide (l < ns + uWords.length)) && nw.all (fun l => decide (l < ns)) &&
    Δ.all (fun p => decide (p < n)) &&
    orbOK Δ L (ns + uWords.length) m (wordF L nw)
      (omTwin (fun l lb => insN (lb.map (L l))) (ns + uWords.length) Δ (m + 1) fuel) &&
    (List.range uWords.length).all (fun k => (List.range n).all fun p =>
      L (ns + k) (z p) == z (L (ns + k) p)) &&
    (List.range n).all (fun p => wordF (fun _ => wordF L yw) (List.replicate r 0) p == p) &&
    !(List.range n).all (fun p => wordF L yw p == p) &&
    (List.range n).all (fun p => wordF L yw (z p) == z (wordF L yw p)) &&
    !(List.range n).all (fun p => wordF L yw (wordF L nw p) == wordF L nw (wordF L yw p))

theorem rChkF_of_split {n : Nat} {Δ : List Nat} {L : Nat → Nat → Nat} {ns : Nat}
    {AB : Nat → Nat → Nat} {z : Nat → Nat} {uWords : List (List Nat)} {yw nw : List Nat}
    {r m fuel : Nat} (h1 : rWordsF n L ns AB uWords = true)
    (h2 : rRestF n Δ L ns z uWords yw nw r m fuel = true) :
    CFSG.KC.SLOm.rChkF n Δ L ns AB z uWords yw nw r m fuel = true := by
  unfold rWordsF at h1
  unfold rRestF at h2
  unfold CFSG.KC.SLOm.rChkF
  simp only [Bool.and_eq_true, h1, and_true] at h2 ⊢
  exact h2

theorem r_okW : rWordsF 8330 L 4 AB heUWords = true := by
  quickRfl

theorem r_okR : rRestF 8330 heDelta L 4 Z heUWords heYWord heNWord 7 21 100 = true := by
  quickRfl

theorem r_ok : rChkF 8330 heDelta L 4 AB Z heUWords heYWord heNWord 7 21 100 = true :=
  rChkF_of_split r_okW r_okR

theorem nc_ok : ncChkF 8330 (AB 0) Z = true := by
  quickRfl

end CFSG.KD.E68S4215.He

end
