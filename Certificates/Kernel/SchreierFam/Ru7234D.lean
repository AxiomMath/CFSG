module

public import Certificates.Kernel.SporSch.GenPerms
public import Certificates.Kernel.Sporadic.IntWordsCmd
public import CFSG.Certificates.Kernel.Spor.PackWord
public import CFSG.Quasithin.Vol2.KGFactC31RuConfCheck
public meta import CFSG.Quasithin.Vol2.KGFactC31RuConfCheck
public meta import CFSG.Assembly.QuasithinDefs
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Foundations
public meta import CFSG.Foundations
public meta import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public meta import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public meta import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public meta import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public meta import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public meta import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public meta import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public meta import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public meta import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public meta import CFSG.Quasithin.Background.A3ComponentsAmbient
public meta import CFSG.Quasithin.Background.B2Thompson
public import CFSG.Quasithin.Background.B2Thompson
public import CFSG.Sporadic.HeldB.Common
public meta import CFSG.Sporadic.HeldB.Common
public meta import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public meta import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public meta import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public meta import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43
public meta import Certificates.Certificate43

public section

namespace CertificateChecks.KernelSchreierFam.Ru7234

open CFSG.Quasithin.KGC31.Ru CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native

meta def bM : Array (Array Nat) := b64A.toArray ++ b64A.toArray.map ruInv

meta def uM : Array (Array Nat) := u33A ++ u33A.map ruInv

meta def tM : Array (Array Nat) := #[t64A]

meta def spM : Array (Array Nat) := sp64.toArray

meta def invM (t : Array Nat) : Array Nat := invCand 4060 t

meta def orbWords (S : Array (Array Nat)) (ls : List Int) (b : Nat) : Array (Option (List Int)) :=
  Id.run do
    let arr := fun (l : Int) => if 0 < l then S[l.toNat - 1]! else invM S[(-l).toNat - 1]!
    let mut ws : Array (Option (List Int)) := (Array.replicate 4060 none).set! b (some [])
    let mut queue : Array Nat := #[b]
    let mut h := 0
    for _ in [0:4060] do
      if h < queue.size then
        let x := queue[h]!
        h := h + 1
        let wx := (ws[x]!).getD []
        for l in ls do
          let y := (arr l)[x]!
          if (ws[y]!).isNone then
            ws := ws.set! y (some (l :: wx))
            queue := queue.push y
    return ws

meta def siftWord (S : Array (Array Nat)) (base : Array Nat) (t : Array Nat) : List Int := Id.run do
  let mut cur := t
  let mut out : List Int := []
  for i in [0:base.size] do
    let idx := (List.range S.size).filter fun j =>
      (List.range i).all fun s => (S[j]!)[base[s]!]! == base[s]!
    let ls : List Int := idx.flatMap fun j => [(j : Int) + 1, -((j : Int) + 1)]
    let ws := orbWords S ls base[i]!
    let w := (ws[cur[base[i]!]!]!).getD []
    let u := wordA 4060 S (S.map invM) w
    cur := compA 4060 (invM u) cur
    out := out ++ w
  return out

meta def memM : Array (List Int) := (b64A.toArray ++ u33A).map (siftWord m64S #[0, 1])

meta def conjIdxM : List Nat := (List.range 64).map fun k =>
  if k == 0 then 0 else
    ((List.range conjT64W.length).find? fun i =>
      let c := wM (conjT64W.getD i [])
      eqA 4060 (cjA c (ruInv c) t64A) (sp64.getD k #[])).getD 0

meta def spIdx (t : Array Nat) : Nat :=
  ((List.range 64).find? fun k => eqA 4060 (sp64.getD k #[]) t).getD 64

meta def normIdxM : List Nat := (List.range 30).map fun a =>
  spIdx (cjA m64S[a / 6]! (ruInv m64S[a / 6]!) (b64A.getD (a % 6) #[]))

meta def relIdxM : List Nat := CFSG.Quasithin.u33PresRels.map fun r => spIdx (relA r)

end CertificateChecks.KernelSchreierFam.Ru7234

#knatlist CertificateChecks.KernelSchreierFam.Ru7234.nIdx
  CertificateChecks.KernelSchreierFam.Ru7234.normIdxM
#knatlist CertificateChecks.KernelSchreierFam.Ru7234.rIdx
  CertificateChecks.KernelSchreierFam.Ru7234.relIdxM
#kss_perms CertificateChecks.KernelSchreierFam.Ru7234.BB 12 CertificateChecks.KernelSchreierFam.Ru7234.bM
#kss_perms CertificateChecks.KernelSchreierFam.Ru7234.UU 12 CertificateChecks.KernelSchreierFam.Ru7234.uM
#kss_perms CertificateChecks.KernelSchreierFam.Ru7234.TT 12 CertificateChecks.KernelSchreierFam.Ru7234.tM
#kss_perms CertificateChecks.KernelSchreierFam.Ru7234.SP 12 CertificateChecks.KernelSchreierFam.Ru7234.spM
#kc_intwords CertificateChecks.KernelSchreierFam.Ru7234.memL
  CertificateChecks.KernelSchreierFam.Ru7234.memM
#knatlist CertificateChecks.KernelSchreierFam.Ru7234.cIdx
  CertificateChecks.KernelSchreierFam.Ru7234.conjIdxM

end
