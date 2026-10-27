module

public import Certificates.Kernel.LocalComp.Tits.Bind
public import Certificates.Data.Kernel.LocalComp.TitsChain
import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Data.CFSGNative.SectionRank.TitsChain

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.Tits

open CFSG.SectionRank.Native.Tits CFSG.Perm.Native CFSG.Sporadic.Th.Native

meta def lettersM : Array (Array Nat) := (chainLetters ()).map fun t => t.map (·.toNat)

meta def rowsM (i : Nat) : Array (Array Nat) :=
  let T := (chainTreesT ())[i]!
  (Array.range T.pts.size).map fun k => #[ap T.pts k, ap T.par k, ap T.lab k]

meta def posM (i : Nat) : Array (Array Nat) :=
  let T := (chainTreesT ())[i]!
  (Array.range 1755).map fun p => #[if T.pos[p]! == none32 then 65535 else ap T.pos p]

meta def wordsM (i : Nat) : Array (Array Nat) :=
  let T := (chainTreesT ())[i]!
  (Array.range T.pts.size).map fun k => walk T (chainLetters ()) k (checkPts ())

meta def masksM : Array (Array Nat) := (spanMasks (checkVecs ())).map fun v => #[v]

meta def rowsM0 : Array (Array Nat) := rowsM 0
meta def rowsM1 : Array (Array Nat) := rowsM 1
meta def rowsM2 : Array (Array Nat) := rowsM 2
meta def rowsM3 : Array (Array Nat) := rowsM 3
meta def posM0 : Array (Array Nat) := posM 0
meta def posM1 : Array (Array Nat) := posM 1
meta def posM2 : Array (Array Nat) := posM 2
meta def posM3 : Array (Array Nat) := posM 3
meta def wordsM0 : Array (Array Nat) := wordsM 0
meta def wordsM1 : Array (Array Nat) := wordsM 1
meta def wordsM2 : Array (Array Nat) := wordsM 2
meta def wordsM3 : Array (Array Nat) := wordsM 3

end CertificateChecks.KernelLC.Tits

#kmisc_packarrs CertificateChecks.KernelLC.Tits.TL CertificateChecks.KernelLC.Tits.lettersM 11
#kmisc_packarrs CertificateChecks.KernelLC.Tits.TM CertificateChecks.KernelLC.Tits.masksM 60
#kmisc_packarrs CertificateChecks.KernelLC.Tits.TT0 CertificateChecks.KernelLC.Tits.rowsM0 16
#kmisc_packarrs CertificateChecks.KernelLC.Tits.TT1 CertificateChecks.KernelLC.Tits.rowsM1 16
#kmisc_packarrs CertificateChecks.KernelLC.Tits.TT2 CertificateChecks.KernelLC.Tits.rowsM2 16
#kmisc_packarrs CertificateChecks.KernelLC.Tits.TT3 CertificateChecks.KernelLC.Tits.rowsM3 16
#kmisc_packarrs CertificateChecks.KernelLC.Tits.TS0 CertificateChecks.KernelLC.Tits.posM0 16
#kmisc_packarrs CertificateChecks.KernelLC.Tits.TS1 CertificateChecks.KernelLC.Tits.posM1 16
#kmisc_packarrs CertificateChecks.KernelLC.Tits.TS2 CertificateChecks.KernelLC.Tits.posM2 16
#kmisc_packarrs CertificateChecks.KernelLC.Tits.TS3 CertificateChecks.KernelLC.Tits.posM3 16
#kmisc_packarrs CertificateChecks.KernelLC.Tits.TW0 CertificateChecks.KernelLC.Tits.wordsM0 11
#kmisc_packarrs CertificateChecks.KernelLC.Tits.TW1 CertificateChecks.KernelLC.Tits.wordsM1 11
#kmisc_packarrs CertificateChecks.KernelLC.Tits.TW2 CertificateChecks.KernelLC.Tits.wordsM2 11
#kmisc_packarrs CertificateChecks.KernelLC.Tits.TW3 CertificateChecks.KernelLC.Tits.wordsM3 11

public section

namespace CertificateChecks.KernelLC.Tits

@[expose] noncomputable def TTf (i j : Nat) : Nat :=
  nIf(Nat.beq i 0, TT0 j, nIf(Nat.beq i 1, TT1 j, nIf(Nat.beq i 2, TT2 j, TT3 j)))

@[expose] noncomputable def TSf (i j : Nat) : Nat :=
  nIf(Nat.beq i 0, TS0 j, nIf(Nat.beq i 1, TS1 j, nIf(Nat.beq i 2, TS2 j, TS3 j)))

@[expose] noncomputable def TWf (i j : Nat) : Nat :=
  nIf(Nat.beq i 0, TW0 j, nIf(Nat.beq i 1, TW1 j, nIf(Nat.beq i 2, TW2 j, TW3 j)))

@[expose] def szf (i : Nat) : Nat := [1755, 1024, 5, 4].getD i 0

open CFSG.KC.LocalComp.TitsChain in
@[expose] noncomputable def schC (i c : Nat) : Bool :=
  schRange 56 TL TTf TSf TWf szf (tupOf CP) i (levLetters TL CP i) (64 * c) 64

end CertificateChecks.KernelLC.Tits
