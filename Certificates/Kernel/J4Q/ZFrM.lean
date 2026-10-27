module

public import Certificates.Kernel.J4Q.ZFrK
public import Certificates.Kernel.J4Q.VlOk
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.QuasithinUnique.A5 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT
  CFSG.Sporadic.J4.QT2A CFSG.Sporadic.J4.QT2

theorem gw_enc (w : List Int) : WfA (wR w) ∧ encR (wR w) = gwK w := wR_enc w

theorem conjBy_enc {T : Array V2} {t : Nat} (hT : WfA T ∧ encR T = t) (gw : List Int) :
    WfA (zConjBy gw T) ∧ encR (zConjBy gw T) = conjByK gw t :=
  mul_enc hK (mul_enc hK (gw_enc gw) hT) (gw_enc (invW gw))

theorem zfXi_enc : WfA zXi ∧ encR zXi = getN one XG 0 := x0Gen_enc (i := 0) (by decide)

theorem xiI_enc' : WfA zXiInv ∧ encR zXiInv = getN one XG 8 := x0Inv_enc (i := 0) (by decide)

theorem cjRows_enc {T : Array V2} {t : Nat} (hT : WfA T ∧ encR T = t) :
    ∀ n, WfA (zCjRows T n) ∧ encR (zCjRows T n) = cjRowsK t n
  | 0 => hT
  | n + 1 => mul_enc hK (mul_enc hK zfXi_enc (cjRows_enc hT n)) xiI_enc'

theorem ms_enc (hE : ∀ t < 32, etaCK t = true) {T : Array V2} {t : Nat} (hT : WfA T ∧ encR T = t)
    (gw : List Int) (i : Fin 4) : WfA (zMs T gw i) ∧ encR (zMs T gw i) = msK t gw i := by
  obtain ⟨i, hi⟩ := i
  unfold zMs
  cases i with
  | zero => exact ef_enc hE (by decide)
  | succ n => exact conjBy_enc (cjRows_enc hT (n + 1)) gw

theorem zfProd_enc{l : List (Array V2)} {L : List Nat}
    (h : List.Forall₂ (fun X x => WfA X ∧ encR X = x) l L) : WfA (zProdRows l) ∧ encR (zProdRows l) = prodK L := by
  induction h with
  | nil => exact id_enc hK
  | cons hx _ ih => exact mul_enc hK hx ih

theorem seqR_enc : ∀ s : List Nat, WfA (zfSeqR s) ∧ encR (zfSeqR s) = seqRK s
  | [] => id_enc hK
  | _ :: s => mul_enc hK (gw_enc _) (seqR_enc s)

theorem seqRi_enc_aux : ∀ (s : List Nat) {A : Array V2} {a : Nat}, (WfA A ∧ encR A = a) →
    WfA (s.foldl (fun acc g => mulRows (wR (invW (zcGenWords.getD g []))) acc) A) ∧
      encR (s.foldl (fun acc g => mulRows (wR (invW (zcGenWords.getD g []))) acc) A) =
        s.foldl (fun acc g => mulJ c rm (gwK (invW (zcGenWords.getD g []))) acc) a
  | [], _, _, h => h
  | _ :: s, _, _, h => seqRi_enc_aux s (mul_enc hK (gw_enc _) h)

theorem seqRi_enc (s : List Nat) : WfA (zfSeqRi s) ∧ encR (zfSeqRi s) = seqRiK s :=
  seqRi_enc_aux s (id_enc hK)

end CertificateChecks.KernelJ4Q

end
