module

public import Certificates.Data.Kernel.Misc.RuSyl8038
public import Certificates.Data.Kernel.Spor.Raw
public import Certificates.Kernel.RuThree.Chain
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelMisc.RuSyl8038

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.RuSyl8038 CertificateChecks.KernelRuThree

@[expose] noncomputable def wv (wd : List Int) : Nat :=
  wordK (nat_lit 4060) (nat_lit 12) (mask (nat_lit 12)) (pidn (nat_lit 4060) (nat_lit 12)) S3R.S
    S3R.SI wd

@[expose] noncomputable def run8038 (u h hi w : List Int) : Bool :=
  strictB (wv u) (fun U => strictB (wv h) (fun H => strictB (wv hi) (fun HI =>
    strictB (wv w) (fun W => core8038 U H HI W))))

theorem ok8038 : run8038 uW hW hWI wW = true := by quickRfl

end CertificateChecks.KernelMisc.RuSyl8038

end
