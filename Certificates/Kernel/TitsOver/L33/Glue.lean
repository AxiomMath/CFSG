module

public import Certificates.Kernel.TitsOver.L33.Checks
public import Certificates.Kernel.TitsOver.Three.Glue
public import CFSG.Certificates.Kernel.Spor.PEnumSound
public import CFSG.Certificates.Kernel.BfsPinAlg
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTitsOver.L33

open CFSG.KC CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MaxD2
open CertificateChecks.KernelTitsOver.Three CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen.TitsL33
open CFSG.HardMathSupport.Dickson.BMRows.M13L33 (l33Rels)
open CFSG.PSL3Four.Native CFSG.StandardType.TitsThree

theorem wT_of {D : Certificates.MaxD2Perm.Data} {K : Pk} (H : Hyps D K) {wd : List Int} {r : Nat}
    (h : wordEqK K.n K.w (mask K.w) (pidn K.n K.w) K.Gp K.GIp K.kG wd r = true) :
    Certificates.MaxD2Perm.wT D wd = unpack K.n K.w r := by
  unfold Certificates.MaxD2Perm.wT Certificates.MaxD2Perm.giT
  rw [H.hDn]
  exact wordT_u ⟨H.hGs, H.hGb⟩ H.hGp h

theorem sz : szOK 1755 11 = true := by quickRfl

theorem id_u : idTab 1755 = unpack 1755 11 (pidn 1755 11) := CFSG.KC.BfsPin.idA_eq sz

theorem ne_id {r : Nat} (hc : canonK 1755 11 (mask 11) (1755 * 11) r = true)
    (hn : Bool.not (Nat.beq r (pidn 1755 11)) = true) :
    (unpack 1755 11 r == unpack 1755 11 (pidn 1755 11)) = false := by
  have hpi := (CFSG.KC.BfsPin.PP.id (n := 1755) (w := 11) sz).1
  cases e : (unpack 1755 11 r == unpack 1755 11 (pidn 1755 11))
  · rfl
  · have e1 := beq_iff_eq.1 e
    have h2 := CFSG.KC.BfsPin.eqA_unpack hc hpi
    rw [e1, CFSG.KC.BfsPin.eqA_unpack hpi hpi, Nat.beq_refl] at h2
    rw [← h2] at hn
    exact absurd hn (by decide)

theorem checkAt {k : Nat} {K : Pk} (H : Hyps (lLocalData k ()) K) (hn : K.n = 1755) (hw : K.w = 11)
    (hrel : (l33Rels.all fun r => wordEqK K.n K.w (mask K.w) (pidn K.n K.w) K.Gp K.GIp K.kG
      (relWord (l33AWords.getD k []) (l33BWords.getD k []) r) (pidn K.n K.w)) = true)
    (ha : bAnd(wordEqK K.n K.w (mask K.w) (pidn K.n K.w) K.Gp K.GIp K.kG (l33AWords.getD k [])
      (wordK K.n K.w (mask K.w) (pidn K.n K.w) K.Gp K.GIp (l33AWords.getD k [])),
      bAnd(canonK 1755 11 (mask 11) (1755 * 11)
        (wordK K.n K.w (mask K.w) (pidn K.n K.w) K.Gp K.GIp (l33AWords.getD k [])),
      Bool.not (Nat.beq (wordK K.n K.w (mask K.w) (pidn K.n K.w) K.Gp K.GIp (l33AWords.getD k []))
        (pidn 1755 11)))) = true) :
    l33CheckAt k = true := by
  simp only [bAnd_iff] at ha
  obtain ⟨ha1, ha2, ha3⟩ := ha
  unfold l33CheckAt
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true']
  refine ⟨fun r hr => ?_, ?_⟩
  · rw [wT_of H (List.all_eq_true.1 hrel r hr), id_u, hn, hw]
    exact beq_self_eq_true _
  · rw [wT_of H ha1, id_u, hn, hw]
    rw [hn, hw] at ha2 ha3
    exact ne_id ha2 ha3

theorem check : titsL33Check () = true := by
  unfold titsL33Check
  simp only [allBelow, List.all_eq_true, List.mem_range]
  intro k hk
  match k, hk with
  | 0, _ => exact checkAt hyps0 rfl rfl relK0 aK0
  | 1, _ => exact checkAt hyps1 rfl rfl relK1 aK1

end CertificateChecks.KernelTitsOver.L33

end
