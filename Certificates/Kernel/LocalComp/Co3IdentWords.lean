module

public import Certificates.Kernel.LocalComp.Co3IdentData
public import Certificates.Kernel.LocalComp.FendelBridge
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentModelInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.FendelSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.Co3Id

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Fendel CFSG.Monster.B.Co2.Native
open CFSG.EvenSmallLie.SympSix.Co3Ident CFSG.Sporadic.Schreier.Co3

@[expose] noncomputable def letP (l : Fin 7 × Bool) : Nat := cond l.2 (P l.1.val) (I l.1.val)

@[expose] noncomputable def wordP : List (Fin 7 × Bool) → Nat
  | [] => pidn 276 9
  | l :: w => pc (letP l) (wordP w)

@[expose] noncomputable def wordOK : List (Fin 7 × Bool) → Bool
  | [] => true
  | l :: w => bAnd(prodOK (letP l) (wordP w) (wordP (l :: w)), wordOK w)

theorem kId : idK 276 9 (mask 9) = true := by quickRfl

theorem letArr_eq (l : Fin 7 × Bool) : letArr l = unpack 276 9 (letP l) := by
  obtain ⟨i, b⟩ := l
  have hi := i.isLt
  cases b
  · obtain ⟨e, _⟩ := invEqK_sound (allN_spec kInv i.val hi)
    unfold letArr letP
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.cond_false]
    rw [bind i.val hi, e]
  · unfold letArr letP
    simp only [↓reduceIte, Bool.cond_true]
    exact bind i.val hi

theorem wordArr_eq : ∀ (w : List (Fin 7 × Bool)), wordOK w = true →
    wordArr w = unpack 276 9 (wordP w)
  | [], _ => by
    unfold wordArr wordP
    exact (idK_sound kId).symm
  | l :: w, h => by
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
    unfold wordArr
    rw [letArr_eq, wordArr_eq w h2, prodOK_eq h1]

end CertificateChecks.KernelLC.Co3Id

end
