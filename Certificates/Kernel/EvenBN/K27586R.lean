module

public import Certificates.Kernel.EvenBN.K27586D
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelEvenBN.NLoc

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CertificateChecks.KernelSpor
open Certificates.TitsAschbacherNLocal

@[expose] noncomputable def sK (X : Nat) : Bool :=
  siftK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsK.LR TitsK.TRI TitsK.BP 5 0 X

theorem vqK : jL.all (fun i => sK (V i) && sK (VQ i) &&
    canonK 1755 11 (mask 11) (1755 * 11) (VQ i) && Nat.beq (pc (VQ i) Pi) (pc Pi (V i))) = true := by
  quickRfl

theorem wK : jL.all (fun j => uL.all fun m => sK (W m j) &&
    canonK 1755 11 (mask 11) (1755 * 11) (W m j)) = true := by quickRfl

theorem kInS : allN 7 (fun j => siftK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsS.LR TitsS.TRI
    TitsS.BP 5 0 (TitsK.S j)) = true := by quickRfl

theorem yK : (permOK 1755 11 (mask 11) (1755 * 11) Y YI &&
    canonK 1755 11 (mask 11) (1755 * 11) YI) = true := by quickRfl

theorem e1 : (sK (pc Pi Pi) && kWords.all (fun w => sK (wP V w))) = true := by quickRfl

theorem e3 : (Nat.beq (pc (wP V [4, 5]) (V 10)) (pc (pc (V 12) (V 10)) (wP V [4, 5])) &&
    Nat.beq (pc (wP V [1, 5]) (V 10)) (pc (pc (V 11) (V 10)) (wP V [1, 5]))) = true := by quickRfl

theorem e6 : (Nat.beq (ppw Y 3) (pidn 1755 11) && !Nat.beq Y (pidn 1755 11) &&
    Nat.beq (pc Y (V 10)) (pc (V 10) Y) && Nat.beq (pc (V 12) Y) (pc Y (V 11)) &&
    Nat.beq (pc (pc (V 11) (V 12)) Y) (pc Y (V 12))) = true := by quickRfl

end CertificateChecks.KernelEvenBN.NLoc

end
