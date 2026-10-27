module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainModSpans
public import Certificates.Kernel.OmegaEight.CohChecks
public import CFSG.Certificates.Kernel.O8CohProved

public section

namespace CertificateChecks.KernelO8.CohCert

open CFSG.KC.O8Coh CFSG.KC.U6F2 CFSG.EvenSmallLie.OmegaEight.Stage1
  CFSG.EvenSmallLie.OmegaEight.Chain CFSG.EvenSmallLie.UnitarySix.YamadaPar

theorem spans_of {n m p c k : ℕ} {Fb f : ℕ → ℕ} {Bcols : Array ℕ} {B E Q : List ℕ}
    (hF : ∀ l < n, Fb (2 ^ l) = f l) (hB : Bcols.toList = B) (hm : B.length = m)
    (hp : Q.length = p) (hn : n = c * k) (hE : E.length = n)
    (h : ∀ i < k, idRowsSeg n B Q ((List.range' (c * i) c).map f) ((E.drop (c * i)).take c)
      (c * i) = true) :
    CertSpans n m p (linBits n p Fb) Bcols := by
  intro x hx
  refine exists_eq_mulVec_of_certCheckWith (Ecols := E.toArray) (Qcols := Q.toArray) ?_ hx
  refine certCheckWith_of_idRowsK_proved (F := (List.range n).map f) (B := B)
    (fun l hl => by rw [getLD_map_range _ _ hl]; exact hF l hl) hB hm (by simpa using hp) ?_
  simpa using idRowsK_of_segs_proved f hn h hE

theorem genP : GenBind .plus gensP := by
  unfold GenBind
  decide +kernel

theorem genM : GenBind .minus gensM := by
  unfold GenBind
  decide +kernel

theorem lettersP : ∀ w ∈ extRels .plus, ∀ s ∈ w, s < 6 := by decide
theorem lettersM : ∀ w ∈ extRels .minus, ∀ s ∈ w, s < 6 := by decide

theorem endSpans_plus : endSpans .plus :=
  spans_of (c := 36) (k := 1) (fun l _ => cobFb6_eq genP _) endP_B endP_len.2.1 endP_len.2.2 rfl
    endP_len.1 endP_seg

theorem endSpans_minus : endSpans .minus :=
  spans_of (c := 36) (k := 1) (fun l _ => cobFb6_eq genM _) endM_B endM_len.2.1 endM_len.2.2 rfl
    endM_len.1 endM_seg

theorem modSpans_plus : modSpans .plus :=
  spans_of (c := 36) (k := 7) (fun l _ => modFb_eq genP _) modP_B modP_len.2.1 modP_len.2.2 rfl
    modP_len.1 modP_seg

theorem modSpans_minus : modSpans .minus :=
  spans_of (c := 36) (k := 7) (fun l _ => modFb_eq genM _) modM_B modM_len.2.1 modM_len.2.2 rfl
    modM_len.1 modM_seg

theorem gamSpans_plus : gamSpans .plus :=
  spans_of (c := 36) (k := 7) (fun l _ => gamFb_eq genP _) gamP_B gamP_len.2.1 gamP_len.2.2 rfl
    gamP_len.1 gamP_seg

theorem gamSpans_minus : gamSpans .minus :=
  spans_of (c := 36) (k := 7) (fun l _ => gamFb_eq genM _) gamM_B gamM_len.2.1 gamM_len.2.2 rfl
    gamM_len.1 gamM_seg

theorem cobB_eq {ε : Eps} {G : List ℕ} (hG : GenBind ε G) :
    (Array.ofFn (n := 36) fun j => cobFb6 ε (2 ^ (j : ℕ))) =
      Array.ofFn (n := 36) fun j => cobK G (2 ^ (j : ℕ)) := by
  congr 1
  funext j
  exact cobFb6_eq hG _

theorem extSpans_plus : extSpans .plus := by
  unfold extSpans
  rw [cobB_eq genP]
  exact spans_of (c := 36) (k := 6) (fun l _ => extFb_eq genP lettersP _) extP_B extP_len.2.1
    extP_len.2.2 rfl extP_len.1 extP_seg

theorem extSpans_minus : extSpans .minus := by
  unfold extSpans
  rw [cobB_eq genM]
  exact spans_of (c := 36) (k := 6) (fun l _ => extFb_eq genM lettersM _) extM_B extM_len.2.1
    extM_len.2.2 rfl extM_len.1 extM_seg

theorem cert3371 : (relCheck6 .plus = true) ∧ (relCheck6 .minus = true) ∧ gamSpans .plus
    ∧ gamSpans .minus ∧ extSpans .plus ∧ extSpans .minus :=
  ⟨relP, relM, gamSpans_plus, gamSpans_minus, extSpans_plus, extSpans_minus⟩

theorem cert3490 : endSpans .plus ∧ endSpans .minus ∧ modSpans .plus ∧ modSpans .minus :=
  ⟨endSpans_plus, endSpans_minus, modSpans_plus, modSpans_minus⟩

end CertificateChecks.KernelO8.CohCert

end
