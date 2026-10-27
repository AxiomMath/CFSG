module

public import Certificates.Kernel.Misc.Lines
public import Certificates.Kernel.Misc.T46
public import CFSG.Certificates.Kernel.Misc.LinesSound

public section

namespace CFSG.KD.Misc.Lines

open CFSG.KC.Misc.Lines CFSG.KD.Misc.T46 CFSG.Fischer.Native

theorem polarLines_true : polarLinesCertificate () = true := by
  rw [polarLines_eq]
  exact lines_sound CFSG.KD.Misc.Unitary.hU pts pos perpAll pl linesAll cnt twins ppAll

end CFSG.KD.Misc.Lines

end
