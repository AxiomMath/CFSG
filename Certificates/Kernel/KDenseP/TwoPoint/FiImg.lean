module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Sporadic.ON2.GenWords
public import CFSG.Certificates.Kernel.Spor.WordsTxtSound
public import CFSG.Monster.Existence.TwoPoint.Fi22Check
public meta import Certificates.Data.CFSGNative.Bridge.Fi23GPL
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Open.MonsterY443Defs
public import CFSG.Sporadic.Co1Base
public import CFSG.Sporadic.Th.F2Spec

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelKDenseP.TwoPoint.FIG CFSG.Sporadic.Bridge.Fi23GPL.Native.imgText

namespace CertificateChecks.KernelKDenseP.TwoPoint

meta def fiImgM : Array (List Int) := CFSG.Sporadic.Bridge.Fi23GPL.Native.imgWords ()

end CertificateChecks.KernelKDenseP.TwoPoint

#kon_words CertificateChecks.KernelKDenseP.TwoPoint.FIW CertificateChecks.KernelKDenseP.TwoPoint.fiImgM

namespace CertificateChecks.KernelKDenseP.TwoPoint

open CFSG.KS.Words

theorem fiImgOK : wordsK FIG.chars FIW.WC FIW.WL 10 = true := by quickRfl

theorem fi_parseWords_eq :
    CFSG.Sporadic.Bridge.Fi23GPL.Native.parseWords = CFSG.Sporadic.Bridge.ONGPL.Native.parseWords :=
  rfl

theorem fi_img_words : CFSG.Sporadic.Bridge.Fi23GPL.Native.imgWords () =
    Array.ofFn (n := 10) fun k => decW (FIW.WC k.val) (FIW.WL k.val) := by
  unfold CFSG.Sporadic.Bridge.Fi23GPL.Native.imgWords
  rw [FIG.eq, fi_parseWords_eq]
  exact wordsK_sound fiImgOK

@[expose] def imgConjB (w : List Int) (m : ℕ) : Bool :=
  w == w.take m ++ CFSG.Monster.Existence.fiDPowWord ++
      CFSG.Monster.Existence.fiInvWord (w.take m) &&
    (w.take m).all fun z => z == 1 || z == -1 || z == 2 || z == -2

theorem imgConjB_ok : imgConjB (decW (FIW.WC 0) (FIW.WL 0)) 27 = true := by quickRfl

theorem fiImgConj_ok : CFSG.Monster.Existence.fiImgConjCheck 0 27 = true := by
  have e : CFSG.Monster.Existence.fiImgConjCheck 0 27 =
      imgConjB (CFSG.Sporadic.Bridge.Fi23GPL.Native.imgWords ())[0]! 27 := rfl
  rw [e, fi_img_words]
  simpa using imgConjB_ok

end CertificateChecks.KernelKDenseP.TwoPoint

end
