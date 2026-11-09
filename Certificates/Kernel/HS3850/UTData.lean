module

public import Certificates.Kernel.SporSch.Th.GenV4
public import Certificates.Data.SmithB45ExcHSData
meta import Certificates.Data.SmithB45ExcHSData

public section

namespace CertificateChecks.KernelHS3850.UT

open CFSG.Quasithin.B45Exc.HS CFSG.Quasithin.B45Exc.Tab CFSG.QuasithinUnique.Setup.X1

meta def inv : List Nat := sylInv 3850 1024 hsSylAl

meta def cm : List Nat := (List.range hsUTab.m).map fun i =>
  (List.range hsUTab.m).foldl (fun acc j => if hsUTab.commAt i j then acc ||| (1 <<< j) else acc) 0

meta def pr : List Nat := (List.range hsUTab.m).map fun i =>
  (List.range hsUTab.m).foldl (fun acc j => acc ||| (hsUTab.prodAt i j <<< (8 * j))) 0

meta def fx : List Nat := hsUFix.toList

meta def keyL : List Nat := hsSylAl.toList.map fun a => a[0]! * 4096 + a[5]!

meta def ks : List Nat := (List.range 1024).mergeSort fun a b => decide (keyL[a]! ≤ keyL[b]!)

meta def kr : List Nat := (List.range 1024).map fun i => ks.idxOf i

meta def ucjTab :Array Nat × Array Nat × Array Nat := Id.run do
  let E := hsSylAl
  let X : Array (Array Nat) := (inv.map fun k => E[k]!).toArray
  let pre := fun (a : Array Nat) (p : Nat) => ((List.range 3850).find? fun y => a[y]! == p).getD 0
  let p0 : Array Nat := (List.range 1024).toArray.map fun m => pre E[m]! 0
  let p5 : Array Nat := (List.range 1024).toArray.map fun m => pre E[m]! 5
  let kA := keyL.toArray
  let mut km : Std.HashMap Nat Nat := {}
  for m in [0:1024] do
    km := km.insert kA[m]! m
  let mut ik : Std.HashMap Nat Nat := {}
  for i in [0:191] do
    let a := X[i]!
    ik := ik.insert (a[0]! * 4096 + a[5]!) i
  let mut rp : Array Nat := Array.replicate 191 191
  let mut cj : Array Nat := Array.replicate 191 0
  let mut ci : Array Nat := Array.replicate 191 0
  for r in [0:191] do
    if rp[r]! == 191 then
      rp := rp.set! r r
      for m in [0:1024] do
        let g := E[m]!
        let x := X[r]!
        let c := ik.getD (g[x[p0[m]!]!]! * 4096 + g[x[p5[m]!]!]!) 191
        if c < 191 && rp[c]! == 191 then
          rp := rp.set! c r
          cj := cj.set! c m
          ci := ci.set! c (km.getD (p0[m]! * 4096 + p5[m]!) 0)
  return (rp, cj, ci)

meta def ucrL : List Nat := ucjTab.1.toList

meta def ucjL : List Nat := ucjTab.2.1.toList

meta def uciL : List Nat := ucjTab.2.2.toList

end CertificateChecks.KernelHS3850.UT

end

set_option maxRecDepth 400000

#kss_natlist CertificateChecks.KernelHS3850.UT.INV CertificateChecks.KernelHS3850.UT.inv
#kss_natlist CertificateChecks.KernelHS3850.UT.CM CertificateChecks.KernelHS3850.UT.cm
#kss_natlist CertificateChecks.KernelHS3850.UT.PR CertificateChecks.KernelHS3850.UT.pr
#kss_natlist CertificateChecks.KernelHS3850.UT.FX CertificateChecks.KernelHS3850.UT.fx
#kss_natlist CertificateChecks.KernelHS3850.UT.KS CertificateChecks.KernelHS3850.UT.ks
#kss_natlist CertificateChecks.KernelHS3850.UT.KR CertificateChecks.KernelHS3850.UT.kr
#kss_natlist CertificateChecks.KernelHS3850.UT.UCR CertificateChecks.KernelHS3850.UT.ucrL
#kss_natlist CertificateChecks.KernelHS3850.UT.UCJ CertificateChecks.KernelHS3850.UT.ucjL
#kss_natlist CertificateChecks.KernelHS3850.UT.UCI CertificateChecks.KernelHS3850.UT.uciL