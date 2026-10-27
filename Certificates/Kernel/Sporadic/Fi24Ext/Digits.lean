module

import CFSG.Certificates.Kernel.Common.Harness
public meta import CFSG.Certificates.Kernel.Common.StrChunks
public import Certificates.Kernel.Sporadic.Fi24Ext.Data
public import Certificates.Data.CFSGNative.Fi24.Data
public import CFSG.Sporadic.Fi24.ExtCertInputs
public import CFSG.Certificates.Kernel.Common.StrChunks

public section

set_option maxRecDepth 10000000

#str_chunks CFSG.KD.Fi24Ext.FA CFSG.Sporadic.Fi24.Native.formData 1048576 10000000 2048

#str_chunks CFSG.KD.Fi24Ext.QA CFSG.Sporadic.Fi24.Native.basisData 65536 10000000 1024

namespace CFSG.KD.Fi24Ext

open CFSG.KC.Fi24FixK

theorem form_digits : digitsOK CTF (nat_lit 152491) FA.chars (nat_lit 0) = true := by quickRfl

theorem basis_digits : digitsOK CTQ (nat_lit 16003) QA.chars (nat_lit 0) = true := by quickRfl

end CFSG.KD.Fi24Ext

end
