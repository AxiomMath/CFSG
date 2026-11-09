module

public import Certificates.Kernel.J4M4.Defs
public import Certificates.Kernel.J4M4.TN
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4M4

open CFSG.KC.J4M4 CFSG.KC.F2W

@[expose] noncomputable def tnRun (i : Nat) : Bool :=
  eqL (msort (((TL.drop (16 * i)).take 16).flatMap fun t => NL.map (mulW 12 t)))
    ((KL.drop (1024 * i)).take 1024)

theorem tLen_k : TL.length = 16 * 16 := Nat.eq_of_beq_eq_true (by quickRfl)

theorem tn_k0 : tnRun 0 = true := by quickRfl
theorem tn_k1 : tnRun 1 = true := by quickRfl
theorem tn_k2 : tnRun 2 = true := by quickRfl
theorem tn_k3 : tnRun 3 = true := by quickRfl
theorem tn_k4 : tnRun 4 = true := by quickRfl
theorem tn_k5 : tnRun 5 = true := by quickRfl
theorem tn_k6 : tnRun 6 = true := by quickRfl
theorem tn_k7 : tnRun 7 = true := by quickRfl
theorem tn_k8 : tnRun 8 = true := by quickRfl
theorem tn_k9 : tnRun 9 = true := by quickRfl
theorem tn_k10 : tnRun 10 = true := by quickRfl
theorem tn_k11 : tnRun 11 = true := by quickRfl
theorem tn_k12 : tnRun 12 = true := by quickRfl
theorem tn_k13 : tnRun 13 = true := by quickRfl
theorem tn_k14 : tnRun 14 = true := by quickRfl
theorem tn_k15 : tnRun 15 = true := by quickRfl

theorem tn_k : ∀ i < 16, tnRun i = true
  | 0, _ => tn_k0 | 1, _ => tn_k1 | 2, _ => tn_k2 | 3, _ => tn_k3
  | 4, _ => tn_k4 | 5, _ => tn_k5 | 6, _ => tn_k6 | 7, _ => tn_k7
  | 8, _ => tn_k8 | 9, _ => tn_k9 | 10, _ => tn_k10 | 11, _ => tn_k11
  | 12, _ => tn_k12 | 13, _ => tn_k13 | 14, _ => tn_k14 | 15, _ => tn_k15
  | _ + 16, h => absurd h (by omega)

theorem ncl_k : NL.all (fun a => eqL (msort (NL.map (mulW 12 a))) NL) = true := by quickRfl

theorem nnorm_k : (List.range 10).all (fun s => eqL (msort (NL.map fun n => mulW 12 n (KG.getD s 0)))
    (msort (NL.map (mulW 12 (KG.getD s 0))))) = true := by quickRfl

theorem tgen_k : subF 20000
    (msort (TL.flatMap fun t => (List.range 10).map fun s => mulW 12 t (KG.getD s 0))) KL = true := by
  quickRfl

end CertificateChecks.KernelJ4M4
