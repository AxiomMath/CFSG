module

public import Certificates.Kernel.Misc.Perm.HexCmd
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Certificates.Data.RouteP.M24Defect
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CertificateChecks.KernelM24Def

open Certificates.RouteP.M24Defect CFSG.Quasithin.H.Mathieu

meta def dcols (a : Array Nat) : Array Nat := (Array.range 11).map fun j => dualAct (matA a) (2 ^ j)

meta def letOf (c : Nat) : Array Nat := letArr (c / 2) (c % 2 == 0)

meta def ldM : Array (Array Nat) := (Array.range 4).map fun c => dcols (letOf c)

meta def lmM : Array (Array Nat) :=
  (Array.range 4).map fun c => (Array.range 11).map fun j => act11 (letOf c) (2 ^ j)

meta def liM : Array (Array Nat) := (Array.range 4).map fun c => letArr (c / 2) (c % 2 != 0)

meta def twV (q : Nat) : Nat :=
  let w := tword (treeTab ()) q
  w.length + 32 * ((w.zipIdx.map fun (l, k) => l.1 * 2 ^ k).sum)

meta def twM : Array (Array Nat) := (Array.range 576).map fun q => #[twV q]

meta def paM : Array (Array Nat) := (Array.range 576).map fun q =>
  let w := tword (treeTab ()) q
  if w.isEmpty then #[0] else
    #[((List.range 576).find? fun p => tword (treeTab ()) p == w.dropLast && p / 24 != p % 24).getD 0]

meta def gqM : Array (Array Nat) :=
  (Array.range 576).map fun q => dcols (wordAInv (tword (treeTab ()) q))

meta def fpM : Array (Array Nat) :=
  (Array.range 576).map fun q => dcols (wordA (tword (treeTab ()) q))

meta def rwM : Array (Array Nat) := relWords.toArray.map fun w =>
  #[w.length] ++ (w.map fun l => 2 * l.1 + (if l.2 then 0 else 1)).toArray

meta def cbM : Array (Array Nat) := (comboData ()).toArray.map fun c =>
  #[c.length] ++ (c.map fun e => e.1 + 1024 * e.2.1 + 8192 * e.2.2).toArray

meta def fsM : Array (Array Nat) := (comboData ()).toArray.map fun c => (comboFs (treeTab ()) c).toArray

meta def laM : Array (Array Nat) := (Array.range 7).map fun i =>
  ((Array.range 11).map fun j => lamApply (2 ^ j, 0) i) ++
    ((Array.range 11).map fun j => lamApply (0, 2 ^ j) i)

meta def sdM : Array (Array Nat) := (sData ()).toArray.map fun v => #[v.1, v.2]

meta def tdM : Array (Array Nat) := (tData ()).toArray.map fun t => t.toArray

meta def chunks : Array (Nat × Nat × Nat) :=
  #[(64, 0, 130), (64, 130, 130), (65, 0, 117), (65, 117, 117), (65, 234, 117), (65, 351, 116),
    (66, 0, 114), (66, 114, 114), (66, 228, 114), (66, 342, 114), (66, 456, 113)]

meta def ckM : Array (Array Nat) := chunks.map fun (r, lo, len) =>
  let ents := (((comboData ())[r]!).drop lo).take len
  #[((comboContribs (treeTab ()) ents).foldl (fun A c => A ^^^ (c.2 <<< (11 * c.1))) 0)]

end CertificateChecks.KernelM24Def

#kmisc_packarrs CertificateChecks.KernelM24Def.LD CertificateChecks.KernelM24Def.ldM 11
#kmisc_packarrs CertificateChecks.KernelM24Def.LM CertificateChecks.KernelM24Def.lmM 11
#kmisc_packarrs CertificateChecks.KernelM24Def.LI CertificateChecks.KernelM24Def.liM 5
#kmisc_packarrs CertificateChecks.KernelM24Def.TW CertificateChecks.KernelM24Def.twM 64
#kmisc_packarrs CertificateChecks.KernelM24Def.PA CertificateChecks.KernelM24Def.paM 16
#kmisc_packarrs CertificateChecks.KernelM24Def.GQ CertificateChecks.KernelM24Def.gqM 11
#kmisc_packarrs CertificateChecks.KernelM24Def.FP CertificateChecks.KernelM24Def.fpM 11
#kmisc_packarrs CertificateChecks.KernelM24Def.RW CertificateChecks.KernelM24Def.rwM 6
#kmisc_packarrs CertificateChecks.KernelM24Def.CB CertificateChecks.KernelM24Def.cbM 24
#kmisc_packarrs CertificateChecks.KernelM24Def.FS CertificateChecks.KernelM24Def.fsM 11
#kmisc_packarrs CertificateChecks.KernelM24Def.LA CertificateChecks.KernelM24Def.laM 11
#kmisc_packarrs CertificateChecks.KernelM24Def.SD CertificateChecks.KernelM24Def.sdM 11
#kmisc_packarrs CertificateChecks.KernelM24Def.TD CertificateChecks.KernelM24Def.tdM 11
#kmisc_packarrs CertificateChecks.KernelM24Def.CK CertificateChecks.KernelM24Def.ckM 16384

end
