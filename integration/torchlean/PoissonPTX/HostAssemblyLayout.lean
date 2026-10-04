import PoissonPTX.HostLayout
import PoissonPTX.AssemblyInputSeparation

namespace PtxTorchLean.Poisson.PTX.Host

def assemblyOutput (probe : Bool) : Field := if probe then .applied else .ap

def Layout.assembly (a : Layout n e w) (probe : Bool) : Assembly.Arena n where
  base:=a.base
  offsets:=a.offset .offsets
  entries:=a.offset .entries
  element:=a.offset .element
  boundary:=a.offset .boundary
  output:=a.offset (assemblyOutput probe)
  bytes:=a.bytes
  entryCount:=e*w*w
  elementCount:=e*w*w
  small:=a.small
  entriesSmall:=by have := a.localSmall; omega
  aligned:=a.baseAligned
  noWrap:=a.noWrap
  offsetAligned:=a.align_width .offsets
  entryAligned:=a.align_width .entries
  elementAligned:=a.aligned _
  boundaryAligned:=a.align_width .boundary
  outputAligned:=a.aligned _
  offsetsFit:=a.fit .offsets
  entriesFit:=a.fit .entries
  elementFit:=a.fit .element
  boundaryFit:=a.fit .boundary
  outputFit:=by cases probe <;> exact a.fit _

theorem Layout.assembly_separated (a : Layout n e w) (probe : Bool) :
    (a.assembly probe).InputSeparation := by
  constructor
  · cases probe
    · exact a.apart .ap .offsets (by decide)
    · exact a.apart .applied .offsets (by decide)
  · cases probe
    · exact a.apart .ap .entries (by decide)
    · exact a.apart .applied .entries (by decide)
  · cases probe
    · exact a.apart .ap .element (by decide)
    · exact a.apart .applied .element (by decide)
  · cases probe
    · exact a.apart .ap .boundary (by decide)
    · exact a.apart .applied .boundary (by decide)

end PtxTorchLean.Poisson.PTX.Host
