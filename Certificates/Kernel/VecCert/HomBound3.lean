module

public import Certificates.Kernel.VecCert.HomBoundG
public import CFSG.Certificates.Kernel.Spor.Mat3Sound

public section

namespace CertificateChecks.KernelHom3

open CFSG.KC.Ord CFSG.KS.Mat3 CertificateChecks.KernelHomG

theorem layout3 {d f N LO RM CI ONE UP : Nat} (hc : consts3OK d f N LO RM CI ONE UP = true) :
    LayoutSound (Canon3 N) (mat3 d N) (mul3s d N LO CI RM) (valid3 N LO) ONE :=
  ⟨fun _ _ hA hB => mul3s_sound hc hA hB, (one3_sound hc).1, (one3_sound hc).2,
    fun _ h => (valid3_iff (consts3_facts hc).2.2.1).1 h⟩

theorem le_range_of_hom3 (P : TauCeti.GroupPresentation)
    {d f N LO RM CI ONE UP Lg Sfin hA hB : Nat} {RB : Nat → Nat}
    {rels : List (List (Nat × Bool))} {MA MB : Matrix (Fin d) (Fin d) (ZMod 3)}
    (hc : consts3OK d f N LO RM CI ONE UP = true)
    (hrelsP : P.relatorLetters = rels) (hgen : P.generatorCount = Lg)
    (hroot : rootsOK RB (valid3 N LO) 1 (Lg + 1) = true)
    (hinv : invsOK RB (mul3s d N LO CI RM) (valid3 N LO) Lg ONE = true)
    (hb : relsBounded rels Lg = true)
    (hr : ∀ r < lenRels rels,
      SegG (Canon3 N) (mat3 d N) Lg RB rels r 0 (lenL (nthRel rels r)) ONE ONE ∨
        ∃ s < r, relDupOK rels s r = true)
    (hregs : RegsInG (Canon3 N) (mat3 d N) Lg RB Sfin)
    (hA0 : 0 < hA) (hAS : hA < Sfin) (hB0 : 0 < hB) (hBS : hB < Sfin)
    (hmA : MA = mat3 d N (RB hA)) (hmB : MB = mat3 d N (RB hB)) :
    ∃ φ : P.Group →* GL (Fin d) (ZMod 3),
      ∀ g : GL (Fin d) (ZMod 3), g.val = MA ∨ g.val = MB → g ∈ φ.range :=
  le_range_of_homG P (layout3 hc) hrelsP hgen hroot hinv hb
    (rels_of_checksG (layout3 hc) hroot hinv hb hr) hregs hA0 hAS hB0 hBS hmA hmB

end CertificateChecks.KernelHom3

end
