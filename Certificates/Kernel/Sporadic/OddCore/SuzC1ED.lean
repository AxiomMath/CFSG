module

public import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
public import Certificates.Kernel.Misc.Perm.HexCmd
meta import CFSG.Sporadic.SuzRecog.C1ModelTests
import CFSG.Open.LocalVocabulary

namespace CertificateChecks.KernelSpor.SuzC1E

open CFSG.Sporadic.SuzRecog.C1Model CFSG.PSL3Four.Native CFSG.KS.PEnumGen CFSG.Sporadic.SuzOddCore

meta def idR : Array Nat := idTab 1782

meta def w0R : Array Nat := w0T

meta def a4G : Array (Array Nat) := #[w0T, rhoT]

meta def t0G : Array (Array Nat) := t0Tabs
meta def v0G : Array (Array Nat) := v0Tabs
meta def b0G : Array (Array Nat) := b0Tabs
meta def b0GI : Array (Array Nat) := b0Invs
meta def nt0G : Array (Array Nat) := nt0Tabs
meta def nt0GI : Array (Array Nat) := nt0Invs

meta def invM : Array (Array Nat) := #[e3xI] ++ v0Enum.tabs.map (invTab 1782)

meta def diffAt (x y : Array Nat) : Nat :=
  ((List.range 1782).find? fun p => !(x[p]! == y[p]!)).map (· + 1) |>.getD 0

meta def commW (x : Array Nat) : Nat :=
  ((List.range 4).findSome? fun j =>
    let d := diffAt (comp 1782 x t0Tabs[j]!) (comp 1782 t0Tabs[j]! x)
    if d == 0 then none else some (1 + 2048 * j + (d - 1))).getD 0

meta def t0Pos (x : Array Nat) : Nat := ((indexOf t0Enum.tabs).getD x 0)

meta def wC : Array Nat := v0Enum.tabs.map commW

meta def wT : Array Nat := v0Enum.tabs.map fun x =>
  if comp 1782 x x == idTab 1782 && !(x == idTab 1782) && !(fixedCount x == 42) then t0Pos x else 0

meta def wL : Array Nat := v0Enum.tabs.map fun x => ((indexOf tcTabs).get? x).map (· + 1) |>.getD 0

meta def wM : Array Nat := v0Enum.tabs.map fun x =>
  if ((indexOf tcTabs).get? x).isSome then 0 else
    let xi := invTab 1782 x
    let i := ((List.range 16).find? fun i =>
      !isJ (comp 1782 (comp 1782 (comp 1782 x c0Tabs[i]!) xi) c0Invs[i]!)).getD 0
    let q := ((List.range 64).find? fun q =>
      let e := t0Enum.tabs[q]!
      let y := conjTab 1782 x xi e
      comp 1782 e e == idTab 1782 && !(comp 1782 e y == comp 1782 y e)).getD 0
    i + 16 * q

meta def wR : Array Nat := (List.range 32).toArray.map fun is =>
  let i := is / 2
  let s := is % 2
  let u := c0Tabs[i]!
  let l := comp 1782 w0T u
  ((List.range 8).find? fun j =>
    comp 1782 kTabs[j]! w0T == comp 1782 (if s = 0 then u else l) kTabs[j]! &&
      (List.range 512).all fun m => rhoCand (comp 1782 kTabs[j]! v0Enum.tabs[m]!) u l).getD 0

meta def wE : Array Nat := #[t0Pos e3T]

meta def c0Pos : Array Nat := ((List.range 512).filter fun k => commT0 v0Enum.tabs[k]!).toArray

meta def rowsOf (a : Array Nat) : Array (Array Nat) :=
  (List.range ((a.size + 31) / 32)).toArray.map fun r =>
    (List.range 32).toArray.map fun t => a.getD (32 * r + t) 0

meta def wCR : Array (Array Nat) := rowsOf wC
meta def wTR : Array (Array Nat) := rowsOf wT
meta def wLR : Array (Array Nat) := rowsOf wL
meta def wMR : Array (Array Nat) := rowsOf wM
meta def wRR : Array (Array Nat) := rowsOf wR
meta def wER : Array (Array Nat) := rowsOf wE

meta def c0PosL : List Nat := c0Pos.toList

end CertificateChecks.KernelSpor.SuzC1E

public section

set_option maxRecDepth 400000

#kpenum CertificateChecks.KernelSpor.SuzC1ET 1782 11 false CertificateChecks.KernelSpor.SuzC1E.t0G
  CertificateChecks.KernelSpor.SuzC1E.t0G CertificateChecks.KernelSpor.SuzC1E.idR 64
#kpenum CertificateChecks.KernelSpor.SuzC1EV 1782 11 false CertificateChecks.KernelSpor.SuzC1E.v0G
  CertificateChecks.KernelSpor.SuzC1E.v0G CertificateChecks.KernelSpor.SuzC1E.idR 512
#kpenum CertificateChecks.KernelSpor.SuzC1EA 1782 11 false CertificateChecks.KernelSpor.SuzC1E.a4G
  CertificateChecks.KernelSpor.SuzC1E.a4G CertificateChecks.KernelSpor.SuzC1E.idR 12
#kpenum CertificateChecks.KernelSpor.SuzC1EB 1782 11 true CertificateChecks.KernelSpor.SuzC1E.b0G
  CertificateChecks.KernelSpor.SuzC1E.b0GI CertificateChecks.KernelSpor.SuzC1E.w0R 3
#kpenum CertificateChecks.KernelSpor.SuzC1EN 1782 11 true CertificateChecks.KernelSpor.SuzC1E.nt0G
  CertificateChecks.KernelSpor.SuzC1E.nt0GI CertificateChecks.KernelSpor.SuzC1E.w0R 24

#kmisc_packarrs CertificateChecks.KernelSpor.SuzC1EI CertificateChecks.KernelSpor.SuzC1E.invM 11

#kmisc_packarrs CertificateChecks.KernelSpor.SuzC1EWC CertificateChecks.KernelSpor.SuzC1E.wCR 32
#kmisc_packarrs CertificateChecks.KernelSpor.SuzC1EWT CertificateChecks.KernelSpor.SuzC1E.wTR 32
#kmisc_packarrs CertificateChecks.KernelSpor.SuzC1EWL CertificateChecks.KernelSpor.SuzC1E.wLR 32
#kmisc_packarrs CertificateChecks.KernelSpor.SuzC1EWM CertificateChecks.KernelSpor.SuzC1E.wMR 32
#kmisc_packarrs CertificateChecks.KernelSpor.SuzC1EWR CertificateChecks.KernelSpor.SuzC1E.wRR 32
#kmisc_packarrs CertificateChecks.KernelSpor.SuzC1EWE CertificateChecks.KernelSpor.SuzC1E.wER 32

#knatlist CertificateChecks.KernelSpor.SuzC1EC CertificateChecks.KernelSpor.SuzC1E.c0PosL

end
