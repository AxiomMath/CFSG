module

public import Certificates.Data.Kernel.LocLn.Defs
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 400000

#kc_repo #kc_blocked_root CertificateChecks.KernelLocL43.TT "Certificates/Kernel/LocL43/data/pts.bin"
  3 9
  13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084095
  32768 13203227659935748072

#kc_repo #kc_blocked_root CertificateChecks.KernelLocL43.OT "Certificates/Kernel/LocL43/data/tab.bin"
  6 4 65535 9774 18029891973463861266

#kc_repo #kc_blocked_root CertificateChecks.KernelLocL43.CT "Certificates/Kernel/LocL43/data/cv.bin"
  6 5 4294967295 76160 340859650456452415

#kc_repo #kc_blocked_root CertificateChecks.KernelLocL43.RP "Certificates/Kernel/LocL43/data/rep.bin"
  3 9
  13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084095
  4864 18062829725898205223

namespace CertificateChecks.KernelLocL43

open CFSG.KD.LocLn

@[expose] noncomputable def G (k : Nat) : Nat :=
  nIf(Nat.beq k 0, 116246168933069967077958060782799292315613682620862227231759017877221031280641,
  nIf(Nat.beq k 1, 116247949583732338358332446639443132607835916115085672894286760701075954663425,
  nIf(Nat.beq k 2, 116696721890254283843306165241158211439658717255136152084486022664888512545024,
    115792096139062545440614200071938219415712993672133743969901476044242497372160)))

@[expose] noncomputable def T (i : Nat) : Nat := TT i

@[expose] noncomputable def E (i k : Nat) : Nat := OT (Nat.add (Nat.mul 4 i) k)

@[expose] noncomputable def PA (i : Nat) : Nat := OT (Nat.add 2048 i)

@[expose] noncomputable def LA (i : Nat) : Nat := OT (Nat.add 2560 i)

@[expose] noncomputable def SO (i : Nat) : Nat := OT (Nat.add 3072 i)

@[expose] noncomputable def SOI (i : Nat) : Nat := OT (Nat.add 3584 i)

@[expose] noncomputable def F (i : Nat) : Nat := OT (Nat.add 4096 i)

@[expose] noncomputable def O8 (a : Nat) : Nat := OT (Nat.add 4608 a)

@[expose] noncomputable def O2 (b : Nat) : Nat := OT (Nat.add 4768 b)

@[expose] noncomputable def CV (c : Nat) : Nat := CT c

@[expose] noncomputable def RX (r : Nat) : Nat := RP r

@[expose] noncomputable def RT (r : Nat) : Nat := RP (Nat.add 38 r)

@[expose] noncomputable def l43Pt (q : Nat) : Bool :=
  blkN k4 4 512 G T E PA LA SO SOI (Nat.mul 64 q) 64

@[expose] noncomputable def l43Fl (q : Nat) : Bool := flagBlk k4 T F (Nat.mul 64 q) 64

@[expose] noncomputable def l43Pr (q : Nat) : Bool :=
  pairBlk k4 512 38 T O8 O2 CV RX RT 119 (Nat.mul 4 q) 4

end CertificateChecks.KernelLocL43

end
