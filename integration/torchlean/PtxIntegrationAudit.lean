import PoissonPTX.Initialize
import PoissonPTX.InitializeAccess
import PoissonPTX.InitializeAddress
import PoissonPTX.InitializeArena
import PoissonPTX.InitializeCorrect
import PoissonPTX.InitializeEntry
import PoissonPTX.InitializeExists
import PoissonPTX.InitializeInputs
import PoissonPTX.InitializeParallel
import PoissonPTX.InitializePrefix
import PoissonPTX.InitializeRecorded
import PoissonPTX.InitializeState
import PoissonPTX.InitializeText
import PoissonPTX.InitializeValues
import PoissonPTX.StorePair
import PoissonPTX.StoreZero
import PoissonPTX.ArrayArena
import PoissonPTX.ArrayArenaSafety
import PoissonPTX.DividePair
import PoissonPTX.RestartVectors
import PoissonPTX.RestartVectorsAccess
import PoissonPTX.RestartVectorsAddress
import PoissonPTX.RestartVectorsArena
import PoissonPTX.RestartVectorsCorrect
import PoissonPTX.RestartVectorsEntry
import PoissonPTX.RestartVectorsExists
import PoissonPTX.RestartVectorsInputs
import PoissonPTX.RestartVectorsParallel
import PoissonPTX.RestartVectorsRecorded
import PoissonPTX.RestartVectorsState
import PoissonPTX.RestartVectorsText
import PoissonPTX.VectorCopy
import PoissonPTX.ControlFlowScalarSegments
import PoissonPTX.ControlFlowSegments
import PoissonPTX.PreconditionUpdate
import PoissonPTX.PreconditionUpdateCorrect
import PoissonPTX.RegisterUpdate
import PoissonPTX.RegisterUpdateFrame
import PoissonPTX.UpdateXRZ
import PoissonPTX.UpdateXRZAccess
import PoissonPTX.UpdateXRZAddress
import PoissonPTX.UpdateXRZArena
import PoissonPTX.UpdateXRZArenaSafety
import PoissonPTX.UpdateXRZCorrect
import PoissonPTX.UpdateXRZExists
import PoissonPTX.UpdateXRZFootprint
import PoissonPTX.UpdateXRZLayout
import PoissonPTX.UpdateXRZMemory
import PoissonPTX.UpdateXRZNumeric
import PoissonPTX.UpdateXRZParallel
import PoissonPTX.UpdateXRZParallelExists
import PoissonPTX.UpdateXRZPending
import PoissonPTX.UpdateXRZRecorded
import PoissonPTX.UpdateXRZSources
import PoissonPTX.UpdateXRZState
import PoissonPTX.UpdateXRZText
import PoissonPTX.VectorFlowEntry
import PoissonPTX.AffineUpdateAccess
import PoissonPTX.AffineUpdateAddress
import PoissonPTX.AffineUpdateArena
import PoissonPTX.AffineUpdateExists
import PoissonPTX.AffineUpdateParallel
import PoissonPTX.AffineUpdateRecorded
import PoissonPTX.AffineUpdateSources
import PoissonPTX.ObservedParallelNative
import PoissonPTX.ObservedTemporalReplay
import PoissonPTX.AffineUpdate
import PoissonPTX.AffineUpdateCorrect
import PoissonPTX.AffineUpdateEntry
import PoissonPTX.AffineUpdateText
import PoissonPTX.DecodedPublication
import PoissonPTX.DotPublication
import PoissonPTX.DotPublishedComplete
import PoissonPTX.DotZeroReturn
import PoissonPTX.GlobalThreadSourceChecks
import PoissonPTX.GlobalThreadSources
import PoissonPTX.ScalarLoad
import PoissonPTX.VectorEntry
import PoissonPTX.DotComplete
import PoissonPTX.DotCompleteCandidate
import PoissonPTX.DotInitialWave
import PoissonPTX.DotInputRecorded
import PoissonPTX.DotInputTreeCandidate
import PoissonPTX.DotInputWave
import PoissonPTX.DotOutputExists
import PoissonPTX.DotStageWave
import PoissonPTX.DotTailBody
import PoissonPTX.DotTailGuard
import PoissonPTX.DotTailLane
import PoissonPTX.DotTailWave
import PoissonPTX.DotTreeWitness
import PoissonPTX.DotWitnessAdmission
import PoissonPTX.DotWitnessGuard
import PoissonPTX.DotWitnessLayout
import PoissonPTX.DotWitnessProducers
import PoissonPTX.DotWitnessWords
import PoissonPTX.GlobalSharedAdmission
import PoissonPTX.NativeFlowLayout
import PoissonPTX.NativeFlowLocal
import PoissonPTX.NativeFlowRound
import PoissonPTX.NativeFlowSerial
import PoissonPTX.DotFinalRead
import PoissonPTX.DotNumerics
import PoissonPTX.DotOutputValue
import PoissonPTX.DotSetupRegisters
import PoissonPTX.DotStoreProtection
import PoissonPTX.DotSuffixOrder
import PoissonPTX.DotTreeAddress
import PoissonPTX.DotTreeControl
import PoissonPTX.DotTreeCorrect
import PoissonPTX.DotTreeOwnership
import PoissonPTX.DotTreeReads
import PoissonPTX.DotTreeSources
import PoissonPTX.NativeFlowAccessOrder
import PoissonPTX.NativeFlowEventPrefix
import PoissonPTX.NativeFlowInitialized
import PoissonPTX.NativeFlowProducer
import PoissonPTX.NativeFlowReadBarrier
import PoissonPTX.NativeFlowStageSources
import PoissonPTX.NativeFlowValues
import PoissonPTX.DotBarriers
import PoissonPTX.DotPublicationAddress
import PoissonPTX.DotPublicationRegisters
import PoissonPTX.DotPublicationSafety
import PoissonPTX.DotPublicationSyntax
import PoissonPTX.DotPublicationTrack
import PoissonPTX.DotPublicationValue
import PoissonPTX.DotReturns
import PoissonPTX.NativeFlowBarrier
import PoissonPTX.NativeFlowDecompose
import PoissonPTX.NativeFlowHalting
import PoissonPTX.NativeFlowHistory
import PoissonPTX.NativeFlowPrefixTrack
import PoissonPTX.DotAddress
import PoissonPTX.DotAddressSyntax
import PoissonPTX.DotAddressTail
import PoissonPTX.DotCompletedInput
import PoissonPTX.DotInputAccess
import PoissonPTX.DotInputAdmitted
import PoissonPTX.DotInputFootprint
import PoissonPTX.DotInputObservations
import PoissonPTX.DotProgram
import PoissonPTX.DotProgramRegion
import PoissonPTX.DotProgramText
import PoissonPTX.DotStoreSyntax
import PoissonPTX.DotStores
import PoissonPTX.NativeFlow
import PoissonPTX.NativeFlowFrame
import PoissonPTX.NativeFlowOrigins
import PoissonPTX.NativeFlowPrefix
import PoissonPTX.NativeFlowPrefixComplete
import PoissonPTX.NativeFlowRegion
import PoissonPTX.ControlFlowBoundary
import PoissonPTX.ControlFlowOperandWindow
import PoissonPTX.ControlFlowOperandWindowExists
import PoissonPTX.DotInputBody
import PoissonPTX.DotInputChecks
import PoissonPTX.DotInputComplete
import PoissonPTX.DotInputExists
import PoissonPTX.DotInputLayout
import PoissonPTX.DotInputLoop
import PoissonPTX.DotInputSetup
import PoissonPTX.DotInputText
import PoissonPTX.DotInputTraversal
import PoissonPTX.IndexedScalar
import PoissonPTX.NativeGuard
import PoissonPTX.NativeGuardExists
import PoissonPTX.NativeGuardInvariant
import PoissonPTX.ReductionNative
import PoissonPTX.ReductionNativeCode
import PoissonPTX.ReductionNativeText
import PoissonPTX.ConcurrentValues
import PoissonPTX.ReductionNumerics
import PoissonPTX.ReductionCorrect
import PoissonPTX.ConcurrentLocalBlock
import PoissonPTX.ConcurrentSerialLanes
import PoissonPTX.ReductionLocal
import PoissonPTX.ReductionWitnessWords
import PoissonPTX.ReductionWitnessLayout
import PoissonPTX.ReductionWaves
import PoissonPTX.RepeatedSharedAdmission
import PoissonPTX.ReductionWitnessAdmission
import PoissonPTX.ReductionComplete
import PoissonPTX.ReductionCompleteChecks
import PoissonPTX.ReductionSafety
import PoissonPTX.ConcurrentLimits
import PoissonPTX.ConcurrentAddressHold
import PoissonPTX.ReductionControl
import PoissonPTX.ReductionOwnership
import PoissonPTX.ReductionPublication
import PoissonPTX.ReductionReads
import PoissonPTX.ReductionControlChecks
import PoissonPTX.ReductionSources
import PoissonPTX.ReductionStageSources
import PoissonPTX.ReductionTreeWitness
import PoissonPTX.ReductionTreeSources
import PoissonPTX.ReductionTreeAdmission
import PoissonPTX.ReductionUpdate
import PoissonPTX.ReductionUpdateChecks
import PoissonPTX.RepeatedShared
import PoissonPTX.RepeatedSharedChecks
import PoissonPTX.RepeatedSharedOrderChecks
import PoissonPTX.AssemblyPreservation
import PoissonPTX.CellGridResidualInputs
import PoissonPTX.CellGridResidual
import PoissonPTX.CellGridResidualChecks
import PoissonPTX.CellGridSchedule
import PoissonPTX.CellGridLiftSources
import PoissonPTX.CellGridCandidates
import PoissonPTX.CellGridExists
import PoissonPTX.CellGridExistsChecks
import PoissonPTX.CellGrid
import PoissonPTX.CellGridSources
import PoissonPTX.CellGridPublication
import PoissonPTX.CellGridFamily
import PoissonPTX.CellCandidate
import PoissonPTX.CellCandidateBounds
import PoissonPTX.CellGridIndices
import PoissonPTX.CellGridAdmission
import PoissonPTX.CellGridExecution
import PoissonPTX.CellGridInputs
import PoissonPTX.CellGridAssembly
import PoissonPTX.CellGridReference
import PoissonPTX.CellGridChecks
import PoissonPTX.OperatorArray
import PoissonPTX.OperatorArrayRows
import PoissonPTX.OperatorArrayCorrespondence
import PoissonPTX.CellAssemblyReference
import PoissonPTX.OperatorArrayChecks
import PoissonPTX.SourceCheckWords
import PoissonPTX.AssemblyCompressedRows
import PoissonPTX.AssemblyRowRepresentation
import PoissonPTX.AssemblyMeshRows
import PoissonPTX.AssemblyTableConstruction
import PoissonPTX.AssemblyOperator
import PoissonPTX.AssemblyTableCheck
import PoissonPTX.AssemblyTableChecks
import PoissonPTX.CellExecution
import PoissonPTX.CellTailPadding
import PoissonPTX.CellExecutionStores
import PoissonPTX.CellFamily
import PoissonPTX.OperatorMesh
import PoissonPTX.CellFamilyInputs
import PoissonPTX.CellAssembly
import PoissonPTX.CellAssemblyWitness
import PoissonPTX.CellAssemblyChecks
import PoissonPTX.AssemblyBeforeStore
import PoissonPTX.AssemblyInputSeparation
import PoissonPTX.AssemblyObservedBounds
import PoissonPTX.AssemblyObservedIndexBound
import PoissonPTX.AssemblyObservedOffsets
import PoissonPTX.AssemblyObservedReadAddress
import PoissonPTX.AssemblyOffsetRecords
import PoissonPTX.AssemblyOffsetSources
import PoissonPTX.AssemblyParallelChecks
import PoissonPTX.AssemblyParallelCorrespondence
import PoissonPTX.AssemblyParallelExists
import PoissonPTX.AssemblyParallelReplay
import PoissonPTX.AssemblyReadFields
import PoissonPTX.AssemblyReadFootprints
import PoissonPTX.AssemblyReadSites
import PoissonPTX.AssemblyRecordedWitness
import PoissonPTX.ObservedAccessShape
import PoissonPTX.ObservedParallelExists
import PoissonPTX.ObservedParallelPublication
import PoissonPTX.ObservedPublication
import PoissonPTX.ObservedReadWitness
import PoissonPTX.ObservedWalk
import PoissonPTX.AssemblyArena
import PoissonPTX.AssemblyArenaSafety
import PoissonPTX.AssemblyArenaValues
import PoissonPTX.AssemblyRows
import PoissonPTX.AssemblySnapshotPublication
import PoissonPTX.AssemblyArenaChecks
import PoissonPTX.ControlFlowObserved
import PoissonPTX.ObservedMemoryFrame
import PoissonPTX.ObservedReplay
import PoissonPTX.ObservedExists
import PoissonPTX.ObservedParallel
import PoissonPTX.ObservedParallelReplay
import PoissonPTX.ObservedChecks
import PoissonPTX.AssemblyObservedAddress
import PoissonPTX.AssemblyObservedStores
import PoissonPTX.AssemblyParallelStores
import PoissonPTX.ControlFlowWindow
import PoissonPTX.ControlFlowSequence
import PoissonPTX.AssemblyWindow
import PoissonPTX.AssemblyPrologue
import PoissonPTX.AssemblySetup
import PoissonPTX.AssemblyMask
import PoissonPTX.IndexedFrames
import PoissonPTX.AssemblyOutput
import PoissonPTX.AssemblyEntry
import PoissonPTX.AssemblyEntryResult
import PoissonPTX.ControlFlowWindowExists
import PoissonPTX.AssemblyWindowExists
import PoissonPTX.AssemblyInactive
import PoissonPTX.AssemblyEntryExists
import PoissonPTX.AssemblyEntryChecks
import PoissonPTX.AssemblyEntryText
import PoissonPTX.CellCoefficientRepresentation
import PoissonPTX.CellOperatorCorrespondence
import PoissonPTX.ControlFlow
import PoissonPTX.ControlFlowBlocks
import PoissonPTX.ControlFlowLoop
import PoissonPTX.ControlFlowLoopExists
import PoissonPTX.IndexedBlocks
import PoissonPTX.AssemblyLookup
import PoissonPTX.AssemblyLoop
import PoissonPTX.AssemblyExists
import PoissonPTX.AssemblyLayout
import PoissonPTX.AssemblyChecks
import PoissonPTX.AssemblyText
import PoissonPTX.Relocate
import PoissonPTX.RelocateInverse
import PoissonPTX.RelocateKernel
import PoissonPTX.OffsetExecution
import PoissonPTX.CellWhole
import PoissonPTX.CellWholeCut
import PoissonPTX.RelabelHistory
import PoissonPTX.BarrierClock
import PoissonPTX.ExecutionClock
import PoissonPTX.RelabelShift
import PoissonPTX.CellWholeSources
import PoissonPTX.CellWholeBounds
import PoissonPTX.CellWholeCorrespondence
import PoissonPTX.CellWholeCompose
import PoissonPTX.CellWholeChecks
import PoissonPTX.CellWholeZero
import PoissonPTX.CellWholeText
import PoissonPTX.CellEntryControl
import PoissonPTX.CellEntryActive
import PoissonPTX.CellEntryIndexAddress
import PoissonPTX.CellEntryInputLayout
import PoissonPTX.CellEntryIndexInputs
import PoissonPTX.CellEntrySourceAddress
import PoissonPTX.CellEntryWordInputs
import PoissonPTX.CellEntryJointInputs
import PoissonPTX.CellEntryJointCorrespondence
import PoissonPTX.CellEntryJointChecks
import PoissonPTX.SourceCut
import PoissonPTX.SourceCheck
import PoissonPTX.CellEntryPublication
import PoissonPTX.CellEntryPublishedTensor
import PoissonPTX.CellEntryRebase
import PoissonPTX.CellEntryCorrespondence
import PoissonPTX.CellEntryRebaseChecks
import PoissonPTX.BarrierValue
import PoissonPTX.CellEntryHistory
import PoissonPTX.CellEntryVisibility
import PoissonPTX.CellGatherPreservation
import PoissonPTX.CellEntryContinuation
import PoissonPTX.CellEntryVisibilityChecks
import PoissonPTX.CellEntryStores
import PoissonPTX.CellEntryStorePath
import PoissonPTX.CellEntryOccurrence
import PoissonPTX.CellEntryPadding
import PoissonPTX.CellEntryStoreValue
import PoissonPTX.CellEntryProducers
import PoissonPTX.CellEntryProducerChecks
import PoissonPTX.CellEntryStoreTensor
import PoissonPTX.IndexSources
import PoissonPTX.IndexedCandidate
import PoissonPTX.CellEntry
import PoissonPTX.CellEntryInputs
import PoissonPTX.CellEntryLocal
import PoissonPTX.CellEntryReplay
import PoissonPTX.CellEntryResult
import PoissonPTX.CellEntryBarrier
import PoissonPTX.CellEntryLaunch
import PoissonPTX.CellEntryExec
import PoissonPTX.CellEntryChecks
import PoissonPTX.CellEntryText
import PoissonPTX.Bytes32
import PoissonPTX.IndexedMemory
import PoissonPTX.CellGather
import PoissonPTX.CellGatherLayout
import PoissonPTX.CellGatherText
import PoissonPTX.CellGatherChecks
import PoissonPTX.CellGatherTensor
import PoissonPTX.CellPrologue
import PoissonPTX.CellPrologueEntry
import PoissonPTX.CellPrologueChecks
import PoissonPTX.CellOutputValues
import PoissonPTX.CellOutputOccurrence
import PoissonPTX.GlobalPublication
import PoissonPTX.CellOutputPublication
import PoissonPTX.CellOutputTensor
import PoissonPTX.CellPublicationChecks
import PoissonPTX.CellTailAddressChecks
import PoissonPTX.CellTailOwners
import PoissonPTX.CellTailBounds
import PoissonPTX.CellTailStores
import PoissonPTX.CellTailFrame
import PoissonPTX.CellTailShape
import PoissonPTX.CellTailAddress
import PoissonPTX.CellTailWitnessSources
import PoissonPTX.CellTailChecks
import PoissonPTX.CellTailResult
import PoissonPTX.CellTailProgram
import PoissonPTX.TailExecute
import PoissonPTX.TailRunProjection
import PoissonPTX.TailFrontProjection
import PoissonPTX.ConcurrentTail
import PoissonPTX.ProjectionBuild
import PoissonPTX.ConcurrentProjection
import PoissonPTX.ProjectionChecks
import PoissonPTX.CellCoefficientProgram
import PoissonPTX.CellCoefficientReads
import PoissonPTX.CellOutputSeparation
import PoissonPTX.ConcurrentCut
import PoissonPTX.CellConsumerRun
import PoissonPTX.ConcurrentExtension
import PoissonPTX.CellConsumerChecks
import PoissonPTX.CellConsumerOutput
import PoissonPTX.CellConsumerProgram
import PoissonPTX.CellConsumerSources
import PoissonPTX.CellConsumerValues
import PoissonPTX.CellFinal
import PoissonPTX.CellFinalChecks
import PoissonPTX.CellFinalKernel
import PoissonPTX.CellFinalLayout
import PoissonPTX.CellFinalSnapshot
import PoissonPTX.CellFinalTensor
import PoissonPTX.CellFinalText
import PoissonPTX.Symbolic
import PoissonPTX.SymbolicRun
import PoissonPTX.CellSymbolic
import PoissonPTX.CellLaunch
import PoissonPTX.CellWordView
import PoissonPTX.CellReadGeometry
import PoissonPTX.CellReadValues
import PoissonPTX.CellStoreValues
import PoissonPTX.CellTensor
import PoissonPTX.CellMiddleCorrespondence
import PoissonPTX.ZeroSources
import PoissonPTX.CellMiddleNumericChecks
import PoissonPTX.ConcurrentReplay
import PoissonPTX.ConcurrentReadOnly
import PoissonPTX.ConcurrentComputedStore
import PoissonPTX.CellMiddleInputs
import PoissonPTX.ConcurrentReplayChecks
import PoissonPTX.ConcurrentAddress
import PoissonPTX.ConcurrentPadding
import PoissonPTX.CellMiddle
import PoissonPTX.CellMiddleChecks
import PoissonPTX.CellMiddleWitness
import PoissonPTX.ConcurrentProducer
import PoissonPTX.ConcurrentOwnership
import PoissonPTX.ProducerChecks
import PoissonPTX.ConcurrentOrder
import PoissonPTX.Concurrent
import PoissonPTX.ConcurrentHistory
import PoissonPTX.ConcurrentBarrier
import PoissonPTX.ConcurrentExec
import PoissonPTX.ConcurrentOrigins
import PoissonPTX.BarrierSources
import PoissonPTX.BarrierChecks
import PoissonPTX.SharedStore
import PoissonPTX.SharedPlane
import PoissonPTX.SharedStoreChecks
import PoissonPTX.Contraction
import PoissonPTX.ContractionChecks
import PoissonPTX.ContractionFetched
import PoissonPTX.ContractionLayout
import PoissonPTX.ContractionLoads
import PoissonPTX.ContractionText
import PoissonPTX.Sources
import PoissonPTX.Weak
import PoissonPTX.WeakResidual
import PoissonPTX.WeakPadding
import PoissonPTX.ParallelResidual
import PoissonPTX.ParallelResidualOutput
import PoissonPTX.ParallelResidualLayout
import PoissonPTX.ParallelResidualChecks
import PoissonPTX.Arithmetic
import PoissonPTX.Bytes
import PoissonPTX.Checks
import PoissonPTX.Kernel
import PoissonPTX.Layout
import PoissonPTX.Machine
import PoissonPTX.MemoryBlocks
import PoissonPTX.Residual
import PoissonPTX.ResidualKernel
import PoissonPTX.Tensor
import PoissonPTX.Text
import PoissonBinary64
import PoissonQuadCorrespondence
import PoissonResidualCertificate
import PoissonResidualInput
import PoissonResidualChecks
import PoissonQuadCLI
import PoissonQuadChecks
import PtxHardwareDense
import PtxHardwareDenseChecks
import HardwareDenseMain
import PtxBinary32.BackwardDot
import PtxBinary32.BackwardDotChecks
import PtxBinary32.BackwardDotFinite
import PtxBinary32.PointwiseDifferenceChecks
import PtxBinary32.SoftmaxBackward
import PtxBinary32.SoftmaxBackwardChecks
import PtxBinary32.SoftmaxBackwardDot
import PtxBinary32.SoftmaxBackwardDotChecks
import PtxBinary32.SoftmaxBackwardDotCorrect
import PtxBinary32.SoftmaxBackwardExecutionChecks
import PtxBinary32.SoftmaxBackwardFull
import PtxBinary32.SoftmaxBackwardLayout
import PtxBinary32.SoftmaxBackwardNumeric
import PtxSoftmaxBackward
import PtxSoftmaxBackwardReference
import PtxBinary32.ParallelUnary
import PtxBinary32.ParallelUnaryAdmission
import PtxBinary32.ParallelUnaryChronology
import PtxBinary32.ParallelUnaryControl
import PtxBinary32.ParallelUnaryMemory
import PtxBinary32.SoftmaxParallel
import PtxBinary32.SoftmaxParallelChecks
import PtxBinary32.UnaryPointwiseChecks
import PtxBinary32.UnaryPointwiseContract
import PtxBinary32.UnaryPointwiseControl
import PtxBinary32.UnaryPointwiseCoverage
import PtxBinary32.UnaryPointwiseData
import PtxBinary32.UnaryPointwiseExecution
import PtxBinary32.UnaryPointwiseLaunch
import PtxBinary32.UnaryPointwiseProgram
import PtxBinary32.UnaryPointwiseReads
import PtxBinary32.UnaryPointwiseStored
import PtxBinary32.UnarySequential
import PtxSoftmaxParallel
import PtxBinary32.SoftmaxForwardAccuracy
import PtxBinary32.SoftmaxMemory
import PtxBinary32.SoftmaxMemoryChecks
import PtxBinary32.SoftmaxPipeline
import PtxBinary32.SoftmaxPipelineChecks
import PtxBinary32.SoftmaxPipelineExists
import PtxBinary32.SoftmaxReductions
import PtxBinary32.SoftmaxStorage
import PtxBinary32.SoftmaxSweep
import PtxSoftmaxForward
import PtxSoftmaxPipeline
import PtxBinary32.Normalize
import PtxBinary32.NormalizeChecks
import PtxBinary32.NormalizeCorrect
import PtxBinary32.NormalizeProgram
import PtxBinary32.ShiftedExpRange
import PtxBinary32.SoftmaxNormalize
import PtxBinary32.SumChecks
import PtxBinary32.SumCorrect
import PtxBinary32.SumExecution
import PtxBinary32.SumNormalize
import PtxBinary32.SumProgram
import PtxBinary32.SumTree
import PtxBinary32.SumTreeChecks
import PtxBinary32.Maximum
import PtxBinary32.MaximumAddressControl
import PtxBinary32.MaximumChecks
import PtxBinary32.MaximumControl
import PtxBinary32.MaximumCoverage
import PtxBinary32.MaximumData
import PtxBinary32.MaximumDataMachine
import PtxBinary32.MaximumDataRules
import PtxBinary32.MaximumDataRun
import PtxBinary32.MaximumDataStep
import PtxBinary32.MaximumExecution
import PtxBinary32.MaximumGlobalReads
import PtxBinary32.MaximumLoadControl
import PtxBinary32.MaximumLoadSites
import PtxBinary32.MaximumOwnership
import PtxBinary32.MaximumProgram
import PtxBinary32.MaximumReadData
import PtxBinary32.MaximumReadSources
import PtxBinary32.MaximumSelect
import PtxBinary32.MaximumStoreData
import PtxBinary32.MaximumTree
import PtxBinary32.MaximumUniversal
import PtxBinary32.ShiftedExpChecks
import PtxBinary32.ExponentialInstruction
import PtxBinary32.Exponential
import PtxBinary32.ExponentialChecks
import PtxBinary32.ConservativeULP
import PtxBinary32.ConservativeULPChecks
import PtxBinary32.ExpArgument
import PtxBinary32.ExpArgumentChecks
import PtxBinary32.ReciprocalInstruction
import PtxBinary32.ApproximatePolicyChecks
import PtxBinary32.RoundedReal
import PtxBinary32.ApproximateBounds
import PtxBinary32.RoundedRealChecks
import PtxBinary32.Reciprocal
import PtxBinary32.ReciprocalChecks
import PtxBinary32.Approximate
import PtxBinary32.SoftmaxError
import PtxBinary32.SoftmaxChecks
import PtxSoftmaxAccuracy
import PtxBinary32.CompactDenseAddressControl
import PtxBinary32.CompactDenseControl
import PtxBinary32.CompactDenseDataRules
import PtxBinary32.CompactDenseDataStep
import PtxBinary32.CompactDenseLocalSegments
import PtxBinary32.CompactDenseProgram
import PtxBinary32.DenseLocalSegments
import PtxBinary32.GridAdmission
import PtxBinary32.GridChronology
import PtxBinary32.GridConcrete
import PtxBinary32.GridDenseBackwardChecks
import PtxBinary32.GridDenseBackwardLayout
import PtxBinary32.GridDenseBackwardStorage
import PtxBinary32.GridDenseExists
import PtxBinary32.GridDenseLaunch
import PtxBinary32.GridDenseLocalControl
import PtxBinary32.GridDenseLocalExists
import PtxBinary32.GridPointwiseLogical
import PtxBinary32.GridReplay
import PtxBinary32.GridSources
import PtxBinary32.ParallelSegmentSweep
import PtxGridDenseBackward
import PtxBinary32.GridAccessControl
import PtxBinary32.GridBarrierOrder
import PtxBinary32.GridChecks
import PtxBinary32.GridCompletion
import PtxBinary32.GridControl
import PtxBinary32.GridCoverage
import PtxBinary32.GridDenseAddress
import PtxBinary32.GridDenseChecks
import PtxBinary32.GridDenseCoverage
import PtxBinary32.GridDenseDataMachine
import PtxBinary32.GridDenseDataRun
import PtxBinary32.GridDenseGlobalReads
import PtxBinary32.GridDenseOwnership
import PtxBinary32.GridDenseProgram
import PtxBinary32.GridDenseReadData
import PtxBinary32.GridDenseReadSources
import PtxBinary32.GridDenseUniversal
import PtxBinary32.GridDenseWriter
import PtxBinary32.GridExecution
import PtxBinary32.GridFlatten
import PtxBinary32.GridGraph
import PtxBinary32.GridGraphOrigins
import PtxBinary32.GridGraphUnique
import PtxBinary32.GridHistory
import PtxBinary32.GridInvariants
import PtxBinary32.GridMemory
import PtxBinary32.GridPointwise
import PtxBinary32.GridPointwiseLaunch
import PtxBinary32.GridPointwisePadding
import PtxBinary32.GridReference
import PtxBinary32.GridUnflatten
import PtxGridDenseForward
import PtxBinary32.DenseBackwardChecks
import PtxBinary32.DenseBackwardLayout
import PtxBinary32.DenseBackwardStorage
import PtxBinary32.DenseLaunchContract
import PtxBinary32.PointwiseControl
import PtxBinary32.PointwiseData
import PtxBinary32.PointwiseExists
import PtxBinary32.PointwiseLaunch
import PtxBinary32.PointwiseMachine
import PtxBinary32.PointwiseProgram
import PtxBinary32.PointwiseReads
import PtxBinary32.PointwiseUniversal
import PtxDenseBackward
import PtxBinary32.DenseData
import PtxBinary32.DenseDataFP
import PtxBinary32.DenseDataMachine
import PtxBinary32.DenseDataRules
import PtxBinary32.DenseDataRun
import PtxBinary32.DenseDataStep
import PtxBinary32.DenseGlobalReads
import PtxBinary32.DenseLaunch
import PtxBinary32.DenseLoadControl
import PtxBinary32.DenseLoadSites
import PtxBinary32.DenseReadData
import PtxBinary32.DenseReadSources
import PtxBinary32.DenseStoreData
import PtxBinary32.DenseUniversal
import PtxBinary32.ParallelLoadControl
import PtxBinary32.ParallelWriteValues
import PtxBinary32.ParallelCoverage
import PtxBinary32.DenseCoverage
import PtxBinary32.ParallelAddressControl
import PtxBinary32.ParallelStoreControl
import PtxBinary32.DenseAddressControl
import PtxBinary32.DenseOwnership
import PtxBinary32.ParallelControl
import PtxBinary32.ParallelCompletion
import PtxBinary32.ParallelVisibility
import PtxBinary32.DenseControl
import PtxBinary32.ReductionPadding
import PtxDenseForward
import PtxBinary32.ParallelChronology
import PtxBinary32.ParallelSources
import PtxBinary32.ParallelAdmission
import PtxBinary32.DenseAdmission
import PtxBinary32.ParallelConcrete
import PtxBinary32.ParallelReplay
import PtxBinary32.ParallelReplaySources
import PtxBinary32.DenseReplay
import PtxBinary32.DenseRounds
import PtxBinary32.DenseRoundPhase
import PtxBinary32.DenseOutput
import PtxBinary32.DenseForward
import PtxBinary32.DenseLayout
import PtxBinary32.DenseProgram
import PtxBinary32.DenseAddress
import PtxBinary32.ParallelSegment
import PtxBinary32.DenseSegments
import PtxBinary32.DenseArithmetic
import PtxBinary32.DenseProducts
import PtxBinary32.DenseProductPhase
import PtxBinary32.DenseChecks
import PtxBinary32.ParallelHistory
import PtxBinary32.ParallelMemory
import PtxBinary32.ParallelReference
import PtxBinary32.ParallelPublication
import PtxTensorContext
import PtxDenseVJP
import PtxBinary32.Reduction
import PtxBinary32.ReductionRelu
import PtxBinary32.Parallel
import PtxBinary32.ParallelBarrier
import PtxVectorVJP
import PtxVectorKernel
import PtxVectorAccuracy
import PtxBinary32.DotExamples
import PtxReluAccuracy
import PtxAffineBackward
import PtxAffineSquareKernel
import PtxBinary32.Affine
import PtxBinary32.Mixed
import PtxBinary32.Instructions
import PtxTorchLean
import PtxTensorBridge
import PtxBinary32
import PtxBinary32Examples
import PtxBinary32Bounds
import PtxBinary32Error

/-! Explicit public integration endpoints and binary32 reference dependencies.
Fresh elaboration is checked by check.py; imported build logs are not reused. -/

#print axioms PtxTorchLean.affineSquare
#print axioms PtxTorchLean.forward_polynomial
#print axioms PtxTorchLean.checked_vjp
#print axioms PtxTorchLean.exact_tape_success_vjp
#print axioms PtxTorchLean.checked_success
#print axioms PtxTorchLean.checked_success_vjp
#print axioms PtxTorchLean.unsigned_min_scalar_embedding

#print axioms PtxTorchLean.TensorBridge.view_apply
#print axioms PtxTorchLean.TensorBridge.view_map
#print axioms PtxTorchLean.TensorBridge.layout_bounds
#print axioms PtxTorchLean.TensorBridge.realView_eq_map
#print axioms PtxTorchLean.TensorBridge.completed_unsigned
#print axioms PtxTorchLean.TensorBridge.completed_unsigned_tensor
#print axioms PtxTorchLean.TensorBridge.completed_real_add
#print axioms PtxTorchLean.TensorBridge.completed_bounds
#print axioms PtxTorchLean.TensorBridge.candidate_unsigned_tensor
#print axioms PtxTorchLean.TensorBridge.candidate_execution_agree
#print axioms PtxTorchLean.TensorBridge.execution_exists
#print axioms PtxTorchLean.TensorBridge.real_execution_exists
#print axioms PtxTorchLean.TensorBridge.view_bounded_apply
#print axioms PtxTorchLean.TensorBridge.wraparound_execution
#print axioms PtxTorchLean.TensorBridge.wraparound_not_fitting

#print axioms Ptx.Binary32.encode_decode
#print axioms Ptx.Binary32.decode_encode
#print axioms Ptx.Binary32.finiteReal_none
#print axioms Ptx.Binary32.finiteReal_some
#print axioms Ptx.Binary32.finiteReal_isSome
#print axioms Ptx.Binary32.finite_not_nan
#print axioms Ptx.Binary32.envelope_self
#print axioms Ptx.Binary32.envelope_exists
#print axioms Ptx.Binary32.envelope_nan
#print axioms Ptx.Binary32.envelope_non_nan
#print axioms Ptx.Binary32.envelope_finite_eq
#print axioms Ptx.Binary32.envelope_finite
#print axioms Ptx.Binary32.results_exists
#print axioms Ptx.Binary32.reference_round
#print axioms Ptx.Binary32.results_round
#print axioms Ptx.Binary32.results_abs_error
#print axioms Ptx.Binary32.decode
#print axioms Ptx.Binary32.encode
#print axioms Ptx.Binary32.isNaN
#print axioms Ptx.Binary32.isFinite
#print axioms Ptx.Binary32.finiteReal
#print axioms Ptx.Binary32.Envelope
#print axioms Ptx.Binary32.reference
#print axioms Ptx.Binary32.Results
#print axioms Ptx.Binary32.exact

#print axioms Ptx.Binary32.Examples.signed_zero_bits_distinct
#print axioms Ptx.Binary32.Examples.zero_signs_finite
#print axioms Ptx.Binary32.Examples.smallest_subnormal
#print axioms Ptx.Binary32.Examples.normal_boundary
#print axioms Ptx.Binary32.Examples.ordinary_add
#print axioms Ptx.Binary32.Examples.tie_even_down
#print axioms Ptx.Binary32.Examples.tie_odd_up
#print axioms Ptx.Binary32.Examples.subnormal_add_preserved
#print axioms Ptx.Binary32.Examples.negative_zero_product
#print axioms Ptx.Binary32.Examples.zero_sign_add
#print axioms Ptx.Binary32.Examples.finite_inputs_overflow
#print axioms Ptx.Binary32.Examples.infinity_opposite_invalid
#print axioms Ptx.Binary32.Examples.infinity_times_zero_invalid
#print axioms Ptx.Binary32.Examples.nan_payload_freedom
#print axioms Ptx.Binary32.Examples.signaling_nan_envelope
#print axioms Ptx.Binary32.Examples.exceptional_not_real

#print axioms Ptx.Binary32.Bounds.maxFinite_eq
#print axioms Ptx.Binary32.Bounds.finiteReal_spec
#print axioms Ptx.Binary32.Bounds.reference_finite
#print axioms Ptx.Binary32.Bounds.round_of_range
#print axioms Ptx.Binary32.Bounds.results_error
#print axioms Ptx.Binary32.Bounds.finite_result_exists
#print axioms Ptx.Binary32.Bounds.add_range_of_magnitudes
#print axioms Ptx.Binary32.Bounds.mul_range_of_magnitudes
#print axioms Ptx.Binary32.Bounds.unit_range
#print axioms Ptx.Binary32.Bounds.positive_one_real
#print axioms Ptx.Binary32.Bounds.negative_one_real
#print axioms Ptx.Binary32.Bounds.one_negative_one_results

#print axioms Ptx.Binary32.Error.budget_nonnegative
#print axioms Ptx.Binary32.Error.add_propagation
#print axioms Ptx.Binary32.Error.mul_propagation
#print axioms Ptx.Binary32.Error.add_results
#print axioms Ptx.Binary32.Error.mul_results
#print axioms Ptx.Binary32.Error.add_exists
#print axioms Ptx.Binary32.Error.mul_exists
#print axioms Ptx.Binary32.Error.rounded_add_range
#print axioms Ptx.Binary32.Error.affine_results
#print axioms Ptx.Binary32.Error.affine_exists

#print axioms Ptx.Scalar.Binary32.Instr
#print axioms Ptx.Scalar.Binary32.Occurrence
#print axioms Ptx.Scalar.Binary32.occurrence
#print axioms Ptx.Scalar.Binary32.SupportedTarget
#print axioms Ptx.Scalar.Binary32.Eval
#print axioms Ptx.Scalar.Binary32.Step
#print axioms Ptx.Scalar.Binary32.eval_true_iff
#print axioms Ptx.Scalar.Binary32.eval_false_iff
#print axioms Ptx.Scalar.Binary32.eval_destination
#print axioms Ptx.Scalar.Binary32.eval_frame
#print axioms Ptx.Scalar.Binary32.eval_other
#print axioms Ptx.Scalar.Binary32.eval_event
#print axioms Ptx.Scalar.Binary32.eval_exists
#print axioms Ptx.Scalar.Binary32.step_origin
#print axioms Ptx.Scalar.Binary32.step_exists
#print axioms Ptx.Scalar.Binary32.step_no_fetch
#print axioms Ptx.Scalar.Binary32.step_unsupported_target
#print axioms Ptx.Scalar.Binary32.Text.mnemonic
#print axioms Ptx.Scalar.Binary32.Text.supportedMnemonic
#print axioms Ptx.Scalar.Binary32.Text.decode
#print axioms Ptx.Scalar.Binary32.Text.encode
#print axioms Ptx.Scalar.Binary32.Text.decode_encode
#print axioms Ptx.Scalar.Binary32.Text.decode_iff
#print axioms Ptx.Scalar.Binary32.signed_zero_bits
#print axioms Ptx.Scalar.Binary32.subnormal_bits
#print axioms Ptx.Scalar.Binary32.negative_guard_exec
#print axioms Ptx.Scalar.Binary32.negative_guard_skip
#print axioms Ptx.Scalar.Binary32.alias_add_bits

#print axioms Ptx.Scalar.Mixed.Instr
#print axioms Ptx.Scalar.Mixed.Event
#print axioms Ptx.Scalar.Mixed.Event.memory
#print axioms Ptx.Scalar.Mixed.Event.pc
#print axioms Ptx.Scalar.Mixed.Event.instruction
#print axioms Ptx.Scalar.Mixed.Outcome
#print axioms Ptx.Scalar.Mixed.liftScalar
#print axioms Ptx.Scalar.Mixed.Eval
#print axioms Ptx.Scalar.Mixed.Eligible
#print axioms Ptx.Scalar.Mixed.Dispatch
#print axioms Ptx.Scalar.Mixed.eligible_binary32
#print axioms Ptx.Scalar.Mixed.eval_scalar_iff
#print axioms Ptx.Scalar.Mixed.eval_binary32_iff
#print axioms Ptx.Scalar.Mixed.dispatch_fetch
#print axioms Ptx.Scalar.Mixed.dispatch_missing
#print axioms Ptx.Scalar.Mixed.dispatch_exists
#print axioms Ptx.Scalar.Mixed.Path
#print axioms Ptx.Scalar.Mixed.Advances
#print axioms Ptx.Scalar.Mixed.Path.append
#print axioms Ptx.Scalar.Mixed.Path.invariant
#print axioms Ptx.Scalar.Mixed.Path.event_origin
#print axioms Ptx.Scalar.Mixed.Run
#print axioms Ptx.Scalar.Mixed.Run.not_exhausted
#print axioms Ptx.Scalar.Mixed.scalar_next_iff
#print axioms Ptx.Scalar.Mixed.scalar_halted_iff
#print axioms Ptx.Scalar.Mixed.eval_event_origin
#print axioms Ptx.Scalar.Mixed.dispatch_event_origin
#print axioms Ptx.Scalar.Mixed.eval_next_safe
#print axioms Ptx.Scalar.Mixed.eval_halted
#print axioms Ptx.Scalar.Mixed.dispatch_next_safe
#print axioms Ptx.Scalar.Mixed.dispatch_halted
#print axioms Ptx.Scalar.Mixed.Path.memory_length
#print axioms Ptx.Scalar.Mixed.Path.memory_safe
#print axioms Ptx.Scalar.Mixed.Run.memory_length
#print axioms Ptx.Scalar.Mixed.Run.memory_safe
#print axioms Ptx.Scalar.Mixed.StoresTo
#print axioms Ptx.Scalar.Mixed.eval_frame
#print axioms Ptx.Scalar.Mixed.dispatch_frame
#print axioms Ptx.Scalar.Mixed.Path.frame
#print axioms Ptx.Scalar.Mixed.Run.frame
#print axioms Ptx.Scalar.Mixed.Run.unfold
#print axioms Ptx.Scalar.Mixed.Run.scalar_next_iff
#print axioms Ptx.Scalar.Mixed.Run.scalar_halted_iff
#print axioms Ptx.Scalar.Mixed.Run.binary32_iff

#print axioms Ptx.Scalar.Affine.load
#print axioms Ptx.Scalar.Affine.multiply
#print axioms Ptx.Scalar.Affine.addition
#print axioms Ptx.Scalar.Affine.store
#print axioms Ptx.Scalar.Affine.exit
#print axioms Ptx.Scalar.Affine.program
#print axioms Ptx.Scalar.Affine.Initial
#print axioms Ptx.Scalar.Affine.input
#print axioms Ptx.Scalar.Affine.outputIndex
#print axioms Ptx.Scalar.Affine.afterLeft
#print axioms Ptx.Scalar.Affine.afterRight
#print axioms Ptx.Scalar.Affine.afterBias
#print axioms Ptx.Scalar.Affine.afterMultiply
#print axioms Ptx.Scalar.Affine.afterAdd
#print axioms Ptx.Scalar.Affine.finish
#print axioms Ptx.Scalar.Affine.loadEvent
#print axioms Ptx.Scalar.Affine.trace
#print axioms Ptx.Scalar.Affine.run_iff
#print axioms Ptx.Scalar.Affine.run_exists
#print axioms Ptx.Scalar.Affine.trace_length
#print axioms Ptx.Scalar.Affine.trace_positions
#print axioms Ptx.Scalar.Affine.trace_instructions
#print axioms Ptx.Scalar.Affine.trace_memory
#print axioms Ptx.Scalar.Affine.finish_frame
#print axioms Ptx.Scalar.Affine.finish_registers
#print axioms Ptx.Scalar.Affine.finish_other_register
#print axioms Ptx.Scalar.Affine.finish_output
#print axioms Ptx.Scalar.Affine.finish_other_memory
#print axioms Ptx.Scalar.Affine.run_completed
#print axioms Ptx.Scalar.Affine.stored_error
#print axioms Ptx.Scalar.Affine.advance_pc
#print axioms Ptx.Scalar.Affine.path_control
#print axioms Ptx.Scalar.Affine.path_bound
#print axioms Ptx.Scalar.Affine.memoryProjection
#print axioms Ptx.Scalar.Affine.memoryWitness
#print axioms Ptx.Scalar.Affine.memoryWitness_valid
#print axioms Ptx.Scalar.Affine.trace_memory_witness
#print axioms Ptx.Scalar.Affine.run_memory_witness
#print axioms Ptx.Scalar.Affine.eventAt
#print axioms Ptx.Scalar.Affine.RegisterDependency
#print axioms Ptx.Scalar.Affine.register_dependency_forward
#print axioms Ptx.Scalar.Affine.register_dependency_acyclic
#print axioms Ptx.Scalar.Affine.run_grounded
#print axioms Ptx.Scalar.Affine.disjointFixture
#print axioms Ptx.Scalar.Affine.disjoint_example
#print axioms Ptx.Scalar.Affine.aliasFixture
#print axioms Ptx.Scalar.Affine.all_alias_example

-- Serialized storage, actual two-kernel forward and generated exact backward.
#print axioms Ptx.Scalar.Sequential.Argument
#print axioms Ptx.Scalar.Sequential.Seed
#print axioms Ptx.Scalar.Sequential.start
#print axioms Ptx.Scalar.Sequential.start_pc
#print axioms Ptx.Scalar.Sequential.start_regs
#print axioms Ptx.Scalar.Sequential.start_preds
#print axioms Ptx.Scalar.Sequential.start_memory
#print axioms Ptx.Scalar.Sequential.start_argument
#print axioms Ptx.Scalar.Sequential.start_other
#print axioms Ptx.Scalar.Sequential.Request
#print axioms Ptx.Scalar.Sequential.SuccessfulLaunch
#print axioms Ptx.Scalar.Sequential.SuccessfulLaunch.cell
#print axioms Ptx.Scalar.Sequential.SuccessfulLaunch.present
#print axioms Ptx.Scalar.Sequential.SuccessfulLaunch.owner
#print axioms Ptx.Scalar.Sequential.SuccessfulLaunch.identities
#print axioms Ptx.Scalar.Sequential.SuccessfulLaunch.run
#print axioms Ptx.Scalar.Sequential.SuccessfulLaunch.writeback
#print axioms Ptx.Scalar.Sequential.launch_exists
#print axioms Ptx.Scalar.Sequential.SuccessfulLaunch.exact_writeback
#print axioms Ptx.Scalar.Sequential.SuccessfulLaunch.run_from
#print axioms Ptx.Scalar.Sequential.SuccessfulLaunch.writeback_lookup
#print axioms Ptx.Scalar.Sequential.SuccessfulLaunch.environment_unchanged
#print axioms Ptx.Scalar.Sequential.SuccessfulLaunch.other_cell
#print axioms Ptx.Scalar.Sequential.SuccessfulLaunch.environment_safe
#print axioms Ptx.Scalar.Sequential.SuccessfulLaunch.final_environment_safe
#print axioms Ptx.Scalar.Sequential.SuccessfulLaunch.word_frame
#print axioms Ptx.Scalar.Sequential.SuccessfulLaunch.storage_step
#print axioms Ptx.Scalar.Sequential.no_launch_absent
#print axioms Ptx.Scalar.Sequential.no_launch_wrong_owner
#print axioms Ptx.Scalar.Sequential.no_launch_wrong_identity
#print axioms Ptx.Scalar.Sequential.no_launch_after_release
#print axioms Ptx.Scalar.Sequential.Chain
#print axioms Ptx.Scalar.Sequential.Chain.append
#print axioms Ptx.Scalar.Sequential.Chain.cons_iff
#print axioms Ptx.Scalar.Sequential.Chain.nil_iff
#print axioms Ptx.Scalar.Sequential.Chain.two_iff
#print axioms Ptx.Scalar.Sequential.Chain.storage_history
#print axioms Ptx.Scalar.Sequential.Chain.invariant
#print axioms Ptx.Scalar.Sequential.Chain.old_absent
#print axioms PtxTorchLean.AffineSquareVJP.scalarShape
#print axioms PtxTorchLean.AffineSquareVJP.inputs
#print axioms PtxTorchLean.AffineSquareVJP.graph
#print axioms PtxTorchLean.AffineSquareVJP.sensitivities
#print axioms PtxTorchLean.AffineSquareVJP.forward_value
#print axioms PtxTorchLean.AffineSquareVJP.generated_vjp
#print axioms PtxTorchLean.AffineSquareVJP.forward_tensor
#print axioms PtxTorchLean.AffineSquareVJP.checked_result
#print axioms PtxTorchLean.AffineSquareVJP.sensitivities_adjoint
#print axioms PtxTorchLean.AffineSquareVJP.checked_example
#print axioms Ptx.Binary32.SquareError.roundedAffine
#print axioms Ptx.Binary32.SquareError.Results
#print axioms Ptx.Binary32.SquareError.budget
#print axioms Ptx.Binary32.SquareError.zero_real
#print axioms Ptx.Binary32.SquareError.affine_value
#print axioms Ptx.Binary32.SquareError.budget_expansion
#print axioms Ptx.Binary32.SquareError.results_error
#print axioms Ptx.Binary32.SquareError.results_exists
#print axioms PtxTorchLean.AffineSquareKernel.memory
#print axioms PtxTorchLean.AffineSquareKernel.outputMemory
#print axioms PtxTorchLean.AffineSquareKernel.firstArgs
#print axioms PtxTorchLean.AffineSquareKernel.secondArgs
#print axioms PtxTorchLean.AffineSquareKernel.firstStart
#print axioms PtxTorchLean.AffineSquareKernel.secondStart
#print axioms PtxTorchLean.AffineSquareKernel.request
#print axioms PtxTorchLean.AffineSquareKernel.firstRequest
#print axioms PtxTorchLean.AffineSquareKernel.secondRequest
#print axioms PtxTorchLean.AffineSquareKernel.first_initial
#print axioms PtxTorchLean.AffineSquareKernel.second_initial
#print axioms PtxTorchLean.AffineSquareKernel.first_run_iff
#print axioms PtxTorchLean.AffineSquareKernel.second_run_iff
#print axioms PtxTorchLean.AffineSquareKernel.first_memory
#print axioms PtxTorchLean.AffineSquareKernel.second_memory
#print axioms PtxTorchLean.AffineSquareKernel.launches_correct
#print axioms PtxTorchLean.AffineSquareKernel.pipeline_of_results
#print axioms PtxTorchLean.AffineSquareKernel.pipeline_exists
#print axioms PtxTorchLean.AffineSquareKernel.pipeline_correct
#print axioms PtxTorchLean.AffineSquareKernel.pipeline_frame
#print axioms PtxTorchLean.AffineSquareKernel.stored_forward_error
#print axioms PtxTorchLean.AffineSquareKernel.two_launch_example
#print axioms PtxTorchLean.AffineSquareKernel.second_launch_after_release_rejected

-- Independently authored recomputing backward: executions, values and generated VJP.
#print axioms Ptx.Binary32.BackwardError.roundedProduct
#print axioms Ptx.Binary32.BackwardError.roundedBase
#print axioms Ptx.Binary32.BackwardError.StageRange
#print axioms Ptx.Binary32.BackwardError.Guards
#print axioms Ptx.Binary32.BackwardError.stageBudget
#print axioms Ptx.Binary32.BackwardError.qBudget
#print axioms Ptx.Binary32.BackwardError.baseBudget
#print axioms Ptx.Binary32.BackwardError.parameterBudget
#print axioms Ptx.Binary32.BackwardError.Results
#print axioms Ptx.Binary32.BackwardError.two_real
#print axioms Ptx.Binary32.BackwardError.stage_error
#print axioms Ptx.Binary32.BackwardError.results_error
#print axioms Ptx.Binary32.BackwardError.results_exists
#print axioms Ptx.GradientView.Triple
#print axioms Ptx.GradientView.Words
#print axioms Ptx.GradientView.decode
#print axioms Ptx.GradientView.component
#print axioms Ptx.GradientView.Componentwise
#print axioms Ptx.GradientView.Approximates
#print axioms Ptx.GradientView.component_inputs
#print axioms Ptx.GradientView.componentwise_iff
#print axioms Ptx.GradientView.componentwise_inputs_iff
#print axioms Ptx.GradientView.decode_of_finite
#print axioms Ptx.GradientView.decode_some_iff
#print axioms Ptx.GradientView.decode_none_iff
#print axioms Ptx.GradientView.nonfinite_rejected
#print axioms Ptx.GradientView.not_approximates_of_nonfinite
#print axioms Ptx.GradientView.approximates_iff
#print axioms Ptx.GradientView.generated_iff
#print axioms Ptx.GradientView.generated_of_bounds_checked
#print axioms Ptx.GradientView.signed_zero_same_view
#print axioms Ptx.Scalar.BackwardPipeline.Data
#print axioms Ptx.Scalar.BackwardPipeline.Data.words
#print axioms Ptx.Scalar.BackwardPipeline.Data.left
#print axioms Ptx.Scalar.BackwardPipeline.Data.right
#print axioms Ptx.Scalar.BackwardPipeline.Data.update
#print axioms Ptx.Scalar.BackwardPipeline.outputData
#print axioms Ptx.Scalar.BackwardPipeline.arguments
#print axioms Ptx.Scalar.BackwardPipeline.stageStart
#print axioms Ptx.Scalar.BackwardPipeline.request
#print axioms Ptx.Scalar.BackwardPipeline.requests
#print axioms Ptx.Scalar.BackwardPipeline.Results
#print axioms Ptx.Scalar.BackwardPipeline.stage_initial
#print axioms Ptx.Scalar.BackwardPipeline.stage_run_iff
#print axioms Ptx.Scalar.BackwardPipeline.finish_words
#print axioms Ptx.Scalar.BackwardPipeline.stage_launch_correct
#print axioms Ptx.Scalar.BackwardPipeline.stage_of_results
#print axioms Ptx.Scalar.BackwardPipeline.stage_trace_safe
#print axioms Ptx.Scalar.BackwardPipeline.results_exists
#print axioms Ptx.Scalar.BackwardPipeline.four_launches_iff
#print axioms Ptx.Scalar.BackwardPipeline.launches_correct
#print axioms Ptx.Scalar.BackwardPipeline.pipeline_correct
#print axioms Ptx.Scalar.BackwardPipeline.pipeline_of_results
#print axioms Ptx.Scalar.BackwardPipeline.pipeline_exists
#print axioms Ptx.Scalar.BackwardPipeline.pipeline_other_allocation
#print axioms Ptx.Scalar.BackwardPipeline.words_tail
#print axioms Ptx.Scalar.BackwardPipeline.pipeline_memory_frame
#print axioms Ptx.Scalar.BackwardPipeline.stage_after_release_rejected
#print axioms PtxTorchLean.AffineBackward.Data
#print axioms PtxTorchLean.AffineBackward.recomputeArgs
#print axioms PtxTorchLean.AffineBackward.withSaved
#print axioms PtxTorchLean.AffineBackward.recomputeStart
#print axioms PtxTorchLean.AffineBackward.recomputeRequest
#print axioms PtxTorchLean.AffineBackward.requests
#print axioms PtxTorchLean.AffineBackward.recompute_initial
#print axioms PtxTorchLean.AffineBackward.recompute_run_iff
#print axioms PtxTorchLean.AffineBackward.recompute_memory
#print axioms PtxTorchLean.AffineBackward.recompute_correct
#print axioms PtxTorchLean.AffineBackward.recompute_exists
#print axioms PtxTorchLean.AffineBackward.budgetX
#print axioms PtxTorchLean.AffineBackward.budgetW
#print axioms PtxTorchLean.AffineBackward.budgetB
#print axioms PtxTorchLean.AffineBackward.results_approximate
#print axioms PtxTorchLean.AffineBackward.pipeline_correct
#print axioms PtxTorchLean.AffineBackward.pipeline_exists
#print axioms PtxTorchLean.AffineBackward.pipeline_other_allocation
#print axioms PtxTorchLean.AffineBackward.stored_backward_approximation
#print axioms PtxTorchLean.AffineBackward.fixture
#print axioms PtxTorchLean.AffineBackward.five_launch_example

-- ReLU neuron: actual generated backward, finite gate, execution and accuracy.
#print axioms PtxTorchLean.ReluVJP.scalarShape
#print axioms Ptx.Binary32.Relu.positive
#print axioms Ptx.Binary32.Relu.gate
#print axioms Ptx.Binary32.Relu.forward
#print axioms Ptx.Binary32.Relu.positive_iff
#print axioms Ptx.Binary32.Relu.zero_real
#print axioms Ptx.Binary32.Relu.gate_real
#print axioms Ptx.Binary32.Relu.forward_real
#print axioms Ptx.Binary32.Relu.forward_error
#print axioms Ptx.Binary32.Relu.sign_stable
#print axioms Ptx.Scalar.ReluGate.load
#print axioms Ptx.Scalar.ReluGate.zeroTest
#print axioms Ptx.Scalar.ReluGate.signTest
#print axioms Ptx.Scalar.ReluGate.clear
#print axioms Ptx.Scalar.ReluGate.store
#print axioms Ptx.Scalar.ReluGate.exit
#print axioms Ptx.Scalar.ReluGate.program
#print axioms Ptx.Scalar.ReluGate.Initial
#print axioms Ptx.Scalar.ReluGate.input
#print axioms Ptx.Scalar.ReluGate.afterLeft
#print axioms Ptx.Scalar.ReluGate.afterRight
#print axioms Ptx.Scalar.ReluGate.afterZeroTest
#print axioms Ptx.Scalar.ReluGate.afterZero
#print axioms Ptx.Scalar.ReluGate.afterSignTest
#print axioms Ptx.Scalar.ReluGate.afterClear
#print axioms Ptx.Scalar.ReluGate.finish
#print axioms Ptx.Scalar.ReluGate.run_iff
#print axioms Ptx.Scalar.ReluGate.run_exists
#print axioms Ptx.Scalar.ReluGate.run_memory
#print axioms PtxTorchLean.ReluVJP.inputs
#print axioms PtxTorchLean.ReluVJP.rawGraph
#print axioms PtxTorchLean.ReluVJP.graph
#print axioms PtxTorchLean.ReluVJP.gate
#print axioms PtxTorchLean.ReluVJP.sensitivities
#print axioms PtxTorchLean.ReluVJP.generated_vjp
#print axioms PtxTorchLean.ReluVJP.forward_value
#print axioms PtxTorchLean.ReluVJP.checked_result
#print axioms PtxTorchLean.ReluVJP.graph_correct_at
#print axioms PtxTorchLean.ReluVJP.sensitivities_adjoint
#print axioms PtxTorchLean.ReluKernel.Data
#print axioms PtxTorchLean.ReluKernel.Data.words
#print axioms PtxTorchLean.ReluKernel.Stage
#print axioms PtxTorchLean.ReluKernel.Stage.isGate
#print axioms PtxTorchLean.ReluKernel.program
#print axioms PtxTorchLean.ReluKernel.arguments
#print axioms PtxTorchLean.ReluKernel.Data.update
#print axioms PtxTorchLean.ReluKernel.Results
#print axioms PtxTorchLean.ReluKernel.stageStart
#print axioms PtxTorchLean.ReluKernel.request
#print axioms PtxTorchLean.ReluKernel.forwardStages
#print axioms PtxTorchLean.ReluKernel.backwardStages
#print axioms PtxTorchLean.ReluKernel.Evaluation
#print axioms PtxTorchLean.ReluKernel.run_correct
#print axioms PtxTorchLean.ReluKernel.run_exists
#print axioms PtxTorchLean.ReluKernel.launch_correct
#print axioms PtxTorchLean.ReluKernel.launch_exists
#print axioms PtxTorchLean.ReluKernel.pipeline_correct
#print axioms PtxTorchLean.ReluKernel.pipeline_exists
#print axioms PtxTorchLean.ReluKernel.launch_memory_safe
#print axioms PtxTorchLean.ReluKernel.pipeline_frame
#print axioms PtxTorchLean.ReluKernel.Evaluation.inputs_frame
#print axioms PtxTorchLean.ReluKernel.forward_values
#print axioms PtxTorchLean.ReluKernel.backward_values
#print axioms PtxTorchLean.ReluKernel.Inputs
#print axioms PtxTorchLean.ReluKernel.Inputs.budget
#print axioms PtxTorchLean.ReluKernel.Inputs.affine
#print axioms PtxTorchLean.ReluKernel.forward_accuracy
#print axioms PtxTorchLean.ReluKernel.BackwardInputs
#print axioms PtxTorchLean.ReluKernel.BackwardInputs.actualGate
#print axioms PtxTorchLean.ReluKernel.BackwardInputs.idealGate
#print axioms PtxTorchLean.ReluKernel.BackwardInputs.dxBudget
#print axioms PtxTorchLean.ReluKernel.BackwardInputs.dwBudget
#print axioms PtxTorchLean.ReluKernel.BackwardInputs.away
#print axioms PtxTorchLean.ReluKernel.backward_accuracy
#print axioms PtxTorchLean.ReluKernel.stored_forward_accuracy
#print axioms PtxTorchLean.ReluKernel.stored_backward_accuracy

-- Sequential dot product and all-choice termination certificates.
#print axioms Ptx.Scalar.Mixed.Total
#print axioms Ptx.Scalar.Mixed.Total.mono
#print axioms Ptx.Scalar.Mixed.Total.scalar_next
#print axioms Ptx.Scalar.Mixed.Total.scalar_halt
#print axioms Ptx.Scalar.Mixed.Total.binary32
#print axioms Ptx.Scalar.Mixed.Total.exists_run
#print axioms Ptx.Scalar.Mixed.Total.correct
#print axioms Ptx.Scalar.Mixed.Total.prefix
#print axioms Ptx.Scalar.Mixed.Total.no_infinite
#print axioms Ptx.Scalar.Dot.Fold
#print axioms Ptx.Scalar.Dot.pointer
#print axioms Ptx.Scalar.Dot.initI
#print axioms Ptx.Scalar.Dot.test
#print axioms Ptx.Scalar.Dot.done
#print axioms Ptx.Scalar.Dot.load
#print axioms Ptx.Scalar.Dot.multiply
#print axioms Ptx.Scalar.Dot.addition
#print axioms Ptx.Scalar.Dot.increment
#print axioms Ptx.Scalar.Dot.decrement
#print axioms Ptx.Scalar.Dot.back
#print axioms Ptx.Scalar.Dot.store
#print axioms Ptx.Scalar.Dot.exit
#print axioms Ptx.Scalar.Dot.program
#print axioms Ptx.Scalar.Dot.Stored
#print axioms Ptx.Scalar.Dot.Bounds
#print axioms Ptx.Scalar.Dot.Post
#print axioms Ptx.Scalar.Dot.initial
#print axioms Ptx.Scalar.Dot.total_loop
#print axioms Ptx.Scalar.Dot.total
#print axioms Ptx.Scalar.Dot.execution_exists
#print axioms Ptx.Scalar.Dot.correct
#print axioms Ptx.Scalar.Dot.prefix_termination
#print axioms Ptx.Scalar.Dot.no_infinite_execution
#print axioms Ptx.Scalar.Dot.memory_safe
#print axioms Ptx.Scalar.Dot.other_memory
#print axioms Ptx.Binary32.DotError.Input
#print axioms Ptx.Binary32.DotError.words
#print axioms Ptx.Binary32.DotError.step
#print axioms Ptx.Binary32.DotError.rounded
#print axioms Ptx.Binary32.DotError.ideal
#print axioms Ptx.Binary32.DotError.Safe
#print axioms Ptx.Binary32.DotError.budget
#print axioms Ptx.Binary32.DotError.ideal_cons
#print axioms Ptx.Binary32.DotError.fold_accuracy
#print axioms Ptx.Binary32.DotError.stored_accuracy
#print axioms Ptx.Scalar.Dot.Examples.cancellation
#print axioms Ptx.Scalar.Dot.Examples.reordered
#print axioms Ptx.Scalar.Dot.Examples.cancellation_result
#print axioms Ptx.Scalar.Dot.Examples.reordered_result
#print axioms Ptx.Scalar.Dot.Examples.empty_result
#print axioms Ptx.Scalar.Dot.Examples.cancellationState
#print axioms Ptx.Scalar.Dot.Examples.cancellation_execution
#print axioms Ptx.Scalar.Dot.Examples.zeroInput
#print axioms Ptx.Scalar.Dot.Examples.nonempty_numerical_domain

-- Vector neuron: graph, separately supplied execution, and numerical contracts.
#print axioms PtxTorchLean.VectorVJP.inputs
#print axioms PtxTorchLean.VectorVJP.rawGraph
#print axioms PtxTorchLean.VectorVJP.output
#print axioms PtxTorchLean.VectorVJP.graph
#print axioms PtxTorchLean.VectorVJP.affine
#print axioms PtxTorchLean.VectorVJP.scale
#print axioms PtxTorchLean.VectorVJP.sensitivities
#print axioms PtxTorchLean.VectorVJP.forward_value
#print axioms PtxTorchLean.VectorVJP.generated_vjp
#print axioms PtxTorchLean.VectorVJP.checked_result
#print axioms PtxTorchLean.VectorVJP.graph_correct_at
#print axioms PtxTorchLean.VectorVJP.sensitivities_adjoint
#print axioms PtxTorchLean.VectorKernel.words
#print axioms PtxTorchLean.VectorKernel.slot
#print axioms PtxTorchLean.VectorKernel.weight
#print axioms PtxTorchLean.VectorKernel.input
#print axioms PtxTorchLean.VectorKernel.dx
#print axioms PtxTorchLean.VectorKernel.dw
#print axioms PtxTorchLean.VectorKernel.pairs
#print axioms PtxTorchLean.VectorKernel.Gradient
#print axioms PtxTorchLean.VectorKernel.Gradient.source
#print axioms PtxTorchLean.VectorKernel.Gradient.dest
#print axioms PtxTorchLean.VectorKernel.Stage
#print axioms PtxTorchLean.VectorKernel.Stage.dest
#print axioms PtxTorchLean.VectorKernel.Stage.args
#print axioms PtxTorchLean.VectorKernel.Stage.program
#print axioms PtxTorchLean.VectorKernel.arguments
#print axioms PtxTorchLean.VectorKernel.registers
#print axioms PtxTorchLean.VectorKernel.stageStart
#print axioms PtxTorchLean.VectorKernel.request
#print axioms PtxTorchLean.VectorKernel.Results
#print axioms PtxTorchLean.VectorKernel.Evaluation
#print axioms PtxTorchLean.VectorKernel.forwardStages
#print axioms PtxTorchLean.VectorKernel.gradients
#print axioms PtxTorchLean.VectorKernel.backwardStages
#print axioms PtxTorchLean.VectorKernel.words_length
#print axioms PtxTorchLean.VectorKernel.words_get
#print axioms PtxTorchLean.VectorKernel.words_getBang
#print axioms PtxTorchLean.VectorKernel.words_update
#print axioms PtxTorchLean.VectorKernel.run_correct
#print axioms PtxTorchLean.VectorKernel.run_exists
#print axioms PtxTorchLean.VectorKernel.launch_correct
#print axioms PtxTorchLean.VectorKernel.launch_exists
#print axioms PtxTorchLean.VectorKernel.pipeline_correct
#print axioms PtxTorchLean.VectorKernel.pipeline_exists
#print axioms PtxTorchLean.VectorKernel.launch_memory_safe
#print axioms PtxTorchLean.VectorKernel.pipeline_frame
#print axioms PtxTorchLean.VectorKernel.Evaluation.frame
#print axioms PtxTorchLean.VectorKernel.Gradient.source_ne_slot
#print axioms PtxTorchLean.VectorKernel.Gradient.dest_ne_slot
#print axioms PtxTorchLean.VectorKernel.Gradient.source_ne_dest
#print axioms PtxTorchLean.VectorKernel.Gradient.dest_injective
#print axioms PtxTorchLean.VectorKernel.Evaluation.sources_frame
#print axioms PtxTorchLean.VectorKernel.Evaluation.constants_frame
#print axioms PtxTorchLean.VectorKernel.forward_launches
#print axioms PtxTorchLean.VectorKernel.backward_launches
#print axioms PtxTorchLean.VectorKernel.gradient_values
#print axioms PtxTorchLean.VectorKernel.gradient_header
#print axioms PtxTorchLean.VectorKernel.gradient_mem
#print axioms PtxTorchLean.VectorKernel.forward_values
#print axioms PtxTorchLean.VectorKernel.backward_values
#print axioms PtxTorchLean.VectorKernel.one_real
#print axioms PtxTorchLean.VectorKernel.Inputs
#print axioms PtxTorchLean.VectorKernel.Inputs.x
#print axioms PtxTorchLean.VectorKernel.Inputs.w
#print axioms PtxTorchLean.VectorKernel.Inputs.dot
#print axioms PtxTorchLean.VectorKernel.Inputs.dotBudget
#print axioms PtxTorchLean.VectorKernel.Inputs.idealDot
#print axioms PtxTorchLean.VectorKernel.Inputs.affine
#print axioms PtxTorchLean.VectorKernel.Inputs.budget
#print axioms PtxTorchLean.VectorKernel.Inputs.graph_affine
#print axioms PtxTorchLean.VectorKernel.Inputs.dot_facts
#print axioms PtxTorchLean.VectorKernel.Inputs.affine_facts
#print axioms PtxTorchLean.VectorKernel.forward_accuracy
#print axioms PtxTorchLean.VectorKernel.BackwardInputs
#print axioms PtxTorchLean.VectorKernel.BackwardInputs.actualGate
#print axioms PtxTorchLean.VectorKernel.BackwardInputs.idealGate
#print axioms PtxTorchLean.VectorKernel.BackwardInputs.dxBudget
#print axioms PtxTorchLean.VectorKernel.BackwardInputs.dwBudget
#print axioms PtxTorchLean.VectorKernel.BackwardInputs.dxValue
#print axioms PtxTorchLean.VectorKernel.BackwardInputs.dwValue
#print axioms PtxTorchLean.VectorKernel.BackwardAccuracy
#print axioms PtxTorchLean.VectorKernel.backward_accuracy
#print axioms PtxTorchLean.VectorKernel.BackwardInputs.generated
#print axioms PtxTorchLean.VectorKernel.stored_forward_accuracy
#print axioms PtxTorchLean.VectorKernel.stored_backward_accuracy
#print axioms PtxTorchLean.VectorKernel.Inputs.x_coordinate
#print axioms PtxTorchLean.VectorKernel.Inputs.w_coordinate
#print axioms PtxTorchLean.VectorKernel.stored_backward_adjoint
#print axioms PtxTorchLean.VectorKernel.empty_forward
#print axioms PtxTorchLean.VectorKernel.kink_backward
#print axioms PtxTorchLean.VectorVJP.scalar
#print axioms PtxTorchLean.VectorKernel.Buffer

-- Dense graph, tree arithmetic and fetched repeated-barrier foundations.
#print axioms PtxTorchLean.TensorContext.single_flatten
#print axioms PtxTorchLean.TensorContext.unflatten_single
#print axioms PtxTorchLean.TensorContext.unflatten_add
#print axioms PtxTorchLean.DenseVJP.inputs
#print axioms PtxTorchLean.DenseVJP.rawGraph
#print axioms PtxTorchLean.DenseVJP.output
#print axioms PtxTorchLean.DenseVJP.graph
#print axioms PtxTorchLean.DenseVJP.affine
#print axioms PtxTorchLean.DenseVJP.gate
#print axioms PtxTorchLean.DenseVJP.sensitivities
#print axioms PtxTorchLean.DenseVJP.forward_value
#print axioms PtxTorchLean.DenseVJP.generated_vjp
#print axioms PtxTorchLean.DenseVJP.checked_result
#print axioms PtxTorchLean.DenseVJP.graph_correct_at
#print axioms PtxTorchLean.DenseVJP.sensitivities_adjoint
#print axioms PtxTorchLean.DenseVJP.tensorToVec_get2
#print axioms PtxTorchLean.DenseVJP.affine_coordinate
#print axioms PtxTorchLean.DenseVJP.gate_coordinate
#print axioms PtxTorchLean.DenseVJP.forward_coordinate
#print axioms PtxTorchLean.DenseVJP.backward_coordinates
#print axioms PtxTorchLean.DenseVJP.empty_input_forward
#print axioms PtxTorchLean.DenseVJP.empty_output_dx
#print axioms PtxTorchLean.DenseVJP.gate_at_zero
#print axioms Ptx.Binary32.Reduction.Tree
#print axioms Ptx.Binary32.Reduction.Tree.map
#print axioms Ptx.Binary32.Reduction.Tree.leaves
#print axioms Ptx.Binary32.Reduction.Tree.depth
#print axioms Ptx.Binary32.Reduction.balanced
#print axioms Ptx.Binary32.Reduction.balanced_depth
#print axioms Ptx.Binary32.Reduction.balanced_leaves
#print axioms Ptx.Binary32.Reduction.Eval
#print axioms Ptx.Binary32.Reduction.eval_exists
#print axioms Ptx.Binary32.Reduction.ideal
#print axioms Ptx.Binary32.Reduction.rounded
#print axioms Ptx.Binary32.Reduction.Safe
#print axioms Ptx.Binary32.Reduction.budget
#print axioms Ptx.Binary32.Reduction.words
#print axioms Ptx.Binary32.Reduction.accuracy
#print axioms Ptx.Binary32.Reduction.ideal_leaves
#print axioms Ptx.Binary32.Reduction.RowInput
#print axioms Ptx.Binary32.Reduction.RowInput.affine
#print axioms Ptx.Binary32.Reduction.RowInput.idealAffine
#print axioms Ptx.Binary32.Reduction.RowInput.error
#print axioms Ptx.Binary32.Reduction.RowEval
#print axioms Ptx.Binary32.Reduction.row_eval_exists
#print axioms Ptx.Binary32.Reduction.row_affine_accuracy
#print axioms Ptx.Binary32.Reduction.row_forward_accuracy
#print axioms Ptx.Binary32.Reduction.row_gate_accuracy
#print axioms Ptx.Scalar.Parallel.Space
#print axioms Ptx.Scalar.Parallel.Instr
#print axioms Ptx.Scalar.Parallel.Config
#print axioms Ptx.Scalar.Parallel.Lane
#print axioms Ptx.Scalar.Parallel.State
#print axioms Ptx.Scalar.Parallel.Event
#print axioms Ptx.Scalar.Parallel.Status
#print axioms Ptx.Scalar.Parallel.Outcome
#print axioms Ptx.Scalar.Parallel.setLane
#print axioms Ptx.Scalar.Parallel.arena
#print axioms Ptx.Scalar.Parallel.scalarStep
#print axioms Ptx.Scalar.Parallel.barrierConfig
#print axioms Ptx.Scalar.Parallel.barrierRequest
#print axioms Ptx.Scalar.Parallel.synchronize
#print axioms Ptx.Scalar.Parallel.Dispatch
#print axioms Ptx.Scalar.Parallel.Step
#print axioms Ptx.Scalar.Parallel.Runs
#print axioms Ptx.Scalar.Parallel.dispatch_exists
#print axioms Ptx.Scalar.Parallel.step_exists
#print axioms Ptx.Scalar.Parallel.waiting_blocks
#print axioms Ptx.Scalar.Parallel.fetch_origin
#print axioms Ptx.Scalar.Parallel.Aligned
#print axioms Ptx.Scalar.Parallel.release_aligned
#print axioms Ptx.Scalar.Parallel.reset_aligned
#print axioms Ptx.Scalar.Parallel.setLane_aligned
#print axioms Ptx.Scalar.Parallel.synchronize_aligned
#print axioms Ptx.Scalar.Parallel.dispatch_aligned
#print axioms Ptx.Scalar.Parallel.step_aligned
#print axioms Ptx.Scalar.Parallel.runs_aligned
#print axioms Ptx.Scalar.Parallel.AccessSafe
#print axioms Ptx.Scalar.Parallel.OutcomeSafe
#print axioms Ptx.Scalar.Parallel.scalarStep_safe
#print axioms Ptx.Scalar.Parallel.synchronize_safe
#print axioms Ptx.Scalar.Parallel.dispatch_safe
#print axioms Ptx.Scalar.Parallel.step_safe
#print axioms Ptx.Scalar.Parallel.runs_memory_length
#print axioms Ptx.Scalar.Parallel.runs_access_safe
#print axioms Ptx.Scalar.Parallel.afterRound
#print axioms Ptx.Scalar.Parallel.roundPrefix
#print axioms Ptx.Scalar.Parallel.runs_append
#print axioms Ptx.Scalar.Parallel.barrier_round_exists
#print axioms Ptx.Scalar.Parallel.two_barriers_exist
#print axioms PtxTorchLean.DenseVJP.column
#print axioms PtxTorchLean.DenseVJP.matrix

-- Actual repeated-barrier histories, memory projection and computed publication.
#print axioms Ptx.Scalar.Parallel.History.activeKey
#print axioms Ptx.Scalar.Parallel.History.WaitingOrigin
#print axioms Ptx.Scalar.Parallel.History.CompleteOrigins
#print axioms Ptx.Scalar.Parallel.History.FreshCompletions
#print axioms Ptx.Scalar.Parallel.History.step_history
#print axioms Ptx.Scalar.Parallel.History.runs_history
#print axioms Ptx.Scalar.Parallel.History.completed_arrivals
#print axioms Ptx.Scalar.Parallel.History.Phase
#print axioms Ptx.Scalar.Parallel.History.arrivalPosition
#print axioms Ptx.Scalar.Parallel.History.arrival_position_spec
#print axioms Ptx.Scalar.Parallel.History.certificate
#print axioms Ptx.Scalar.Parallel.History.before_certificate
#print axioms Ptx.Scalar.Parallel.History.after_certificate
#print axioms Ptx.Scalar.Parallel.Memory.slot
#print axioms Ptx.Scalar.Parallel.Memory.location
#print axioms Ptx.Scalar.Parallel.Memory.spaces_distinct
#print axioms Ptx.Scalar.Parallel.Memory.ofEffect
#print axioms Ptx.Scalar.Parallel.Memory.access
#print axioms Ptx.Scalar.Parallel.Memory.access_origin
#print axioms Ptx.Scalar.Parallel.Memory.labels
#print axioms Ptx.Scalar.Parallel.Memory.graph
#print axioms Ptx.Scalar.Parallel.Memory.labels_unique
#print axioms Ptx.Scalar.Parallel.Memory.labels_origin
#print axioms Ptx.Scalar.Parallel.Memory.step_access_complete
#print axioms Ptx.Scalar.Parallel.Memory.run_access_complete
#print axioms Ptx.Scalar.Parallel.Memory.owner
#print axioms Ptx.Scalar.Parallel.Memory.owner_program
#print axioms Ptx.Scalar.Parallel.Memory.order
#print axioms Ptx.Scalar.Parallel.Memory.read_from_unique_writer
#print axioms Ptx.Scalar.Parallel.Memory.run_memory_has_space
#print axioms Ptx.Scalar.Parallel.Memory.run_graph_complete
#print axioms Ptx.Scalar.Parallel.Memory.program_write_origin
#print axioms Ptx.Scalar.Parallel.Memory.runOrder
#print axioms Ptx.Scalar.Parallel.Memory.run_read_from_unique_writer
#print axioms Ptx.Scalar.Parallel.Reference.binary32
#print axioms Ptx.Scalar.Parallel.Reference.binary32_sound
#print axioms Ptx.Scalar.Parallel.Reference.dispatch
#print axioms Ptx.Scalar.Parallel.Reference.dispatch_sound
#print axioms Ptx.Scalar.Parallel.Reference.step
#print axioms Ptx.Scalar.Parallel.Reference.step_sound
#print axioms Ptx.Scalar.Parallel.Reference.run
#print axioms Ptx.Scalar.Parallel.Reference.run_sound
#print axioms Ptx.Scalar.Parallel.Publication.config
#print axioms Ptx.Scalar.Parallel.Publication.program
#print axioms Ptx.Scalar.Parallel.Publication.initial
#print axioms Ptx.Scalar.Parallel.Publication.schedule
#print axioms Ptx.Scalar.Parallel.Publication.execution
#print axioms Ptx.Scalar.Parallel.Publication.execution_sound
#print axioms Ptx.Scalar.Parallel.Publication.completed
#print axioms Ptx.Scalar.Parallel.Publication.successful
#print axioms Ptx.Scalar.Parallel.Publication.labels
#print axioms Ptx.Scalar.Parallel.Publication.labels_actual
#print axioms Ptx.Scalar.Parallel.Publication.source
#print axioms Ptx.Scalar.Parallel.Publication.rank
#print axioms Ptx.Scalar.Parallel.Publication.coherent
#print axioms Ptx.Scalar.Parallel.Publication.graph
#print axioms Ptx.Scalar.Parallel.Publication.order
#print axioms Ptx.Scalar.Parallel.Publication.serial_certificate
#print axioms Ptx.Scalar.Parallel.Publication.admitted
#print axioms Ptx.Scalar.Parallel.Publication.grounded
#print axioms Ptx.Scalar.Parallel.Publication.graph_actual
#print axioms Ptx.Scalar.Parallel.Publication.admitted_execution
#print axioms Ptx.Scalar.Parallel.Publication.memory_safe
#print axioms Ptx.Scalar.Parallel.Memory.Prior.initial
#print axioms Ptx.Scalar.Parallel.Memory.Prior.initial_unique
#print axioms Ptx.Scalar.Parallel.Memory.Prior.memoryKind
#print axioms Ptx.Scalar.Parallel.Memory.Prior.eval_effect_origin

-- Concrete dense program, bounded addresses, actual product phase, and software checks.
#print axioms Ptx.Scalar.Parallel.Dense.Shape
#print axioms Ptx.Scalar.Parallel.Dense.Shape.width
#print axioms Ptx.Scalar.Parallel.Dense.Shape.threads
#print axioms Ptx.Scalar.Parallel.Dense.Shape.weightBase
#print axioms Ptx.Scalar.Parallel.Dense.Shape.biasBase
#print axioms Ptx.Scalar.Parallel.Dense.Shape.outputBase
#print axioms Ptx.Scalar.Parallel.Dense.Shape.globalWords
#print axioms Ptx.Scalar.Parallel.Dense.Shape.sharedWords
#print axioms Ptx.Scalar.Parallel.Dense.Shape.thread
#print axioms Ptx.Scalar.Parallel.Dense.Shape.weight
#print axioms Ptx.Scalar.Parallel.Dense.Shape.scratch
#print axioms Ptx.Scalar.Parallel.Dense.width_positive
#print axioms Ptx.Scalar.Parallel.Dense.thread_bound
#print axioms Ptx.Scalar.Parallel.Dense.thread_injective
#print axioms Ptx.Scalar.Parallel.Dense.weight_bound
#print axioms Ptx.Scalar.Parallel.Dense.global_slices
#print axioms Ptx.Scalar.Parallel.Dense.scratch_bound
#print axioms Ptx.Scalar.Parallel.Dense.scratch_injective
#print axioms Ptx.Scalar.Parallel.Dense.children_bound
#print axioms Ptx.Scalar.Parallel.Dense.word
#print axioms Ptx.Scalar.Parallel.Dense.scalar
#print axioms Ptx.Scalar.Parallel.Dense.guarded
#print axioms Ptx.Scalar.Parallel.Dense.pointer
#print axioms Ptx.Scalar.Parallel.Dense.products
#print axioms Ptx.Scalar.Parallel.Dense.round
#print axioms Ptx.Scalar.Parallel.Dense.output
#print axioms Ptx.Scalar.Parallel.Dense.program
#print axioms Ptx.Scalar.Parallel.Dense.Bounds
#print axioms Ptx.Scalar.Parallel.Dense.config
#print axioms Ptx.Scalar.Parallel.Dense.initial
#print axioms Ptx.Scalar.Parallel.Dense.products_length
#print axioms Ptx.Scalar.Parallel.Dense.round_length
#print axioms Ptx.Scalar.Parallel.Dense.output_length
#print axioms Ptx.Scalar.Parallel.Dense.program_length
#print axioms Ptx.Scalar.Parallel.Dense.round_barrier
#print axioms Ptx.Scalar.Parallel.Dense.product_barrier
#print axioms Ptx.Scalar.Parallel.Dense.output_exit
#print axioms Ptx.Scalar.Parallel.Dense.relu_bits
#print axioms Ptx.Scalar.Parallel.Dense.thread_fits
#print axioms Ptx.Scalar.Parallel.Dense.width_fits
#print axioms Ptx.Scalar.Parallel.Dense.coordinates
#print axioms Ptx.Scalar.Parallel.Dense.decoded_coordinates
#print axioms Ptx.Scalar.Parallel.Dense.bytePointer
#print axioms Ptx.Scalar.Parallel.Dense.pointer_index
#print axioms Ptx.Scalar.Parallel.Dense.pointer_arithmetic
#print axioms Ptx.Scalar.Parallel.Dense.global_output_disjoint
#print axioms Ptx.Scalar.Parallel.Segment
#print axioms Ptx.Scalar.Parallel.Fetches
#print axioms Ptx.Scalar.Parallel.fetches_head
#print axioms Ptx.Scalar.Parallel.fetches_tail
#print axioms Ptx.Scalar.Parallel.Segment.frame
#print axioms Ptx.Scalar.Parallel.Segment.compile
#print axioms Ptx.Scalar.Parallel.Segment.append
#print axioms Ptx.Scalar.Parallel.segmentReference
#print axioms Ptx.Scalar.Parallel.SegmentRegular
#print axioms Ptx.Scalar.Parallel.segmentReference_sound
#print axioms Ptx.Scalar.Parallel.segmentReference_append
#print axioms Ptx.Scalar.Parallel.segmentRegular_append
#print axioms Ptx.Scalar.Parallel.fetches_slice
#print axioms Ptx.Scalar.Parallel.Dense.afterPointer
#print axioms Ptx.Scalar.Parallel.Dense.pointer_execution
#print axioms Ptx.Scalar.Parallel.Dense.afterSetup
#print axioms Ptx.Scalar.Parallel.Dense.setup_execution
#print axioms Ptx.Scalar.Parallel.Dense.afterLoad
#print axioms Ptx.Scalar.Parallel.Dense.guarded_load_execution
#print axioms Ptx.Scalar.Parallel.Dense.afterStore
#print axioms Ptx.Scalar.Parallel.Dense.guarded_store_execution
#print axioms Ptx.Scalar.Parallel.Dense.binary32_regular
#print axioms Ptx.Scalar.Parallel.Dense.operands
#print axioms Ptx.Scalar.Parallel.Dense.nodeValue
#print axioms Ptx.Scalar.Parallel.Dense.affineWord
#print axioms Ptx.Scalar.Parallel.Dense.forwardWord
#print axioms Ptx.Scalar.Parallel.Dense.node_tree
#print axioms Ptx.Scalar.Parallel.Dense.forward_accuracy
#print axioms Ptx.Scalar.Parallel.Dense.weight_index_fits
#print axioms Ptx.Scalar.Parallel.Dense.productFinish
#print axioms Ptx.Scalar.Parallel.Dense.product_segment
#print axioms Ptx.Scalar.Parallel.Dense.products_fetch
#print axioms Ptx.Scalar.Parallel.Dense.product_run
#print axioms Ptx.Scalar.Parallel.Dense.product_memory
#print axioms Ptx.Scalar.Parallel.Dense.product_control
#print axioms Ptx.Scalar.Parallel.Dense.ProductInvariant
#print axioms Ptx.Scalar.Parallel.Dense.product_invariant_step
#print axioms Ptx.Scalar.Parallel.Dense.product_phase_exists
#print axioms Ptx.Scalar.Parallel.Dense.Checks.schedule
#print axioms Ptx.Scalar.Parallel.Dense.Checks.seeds
#print axioms Ptx.Scalar.Parallel.Dense.Checks.check
#print axioms Ptx.Scalar.Parallel.Dense.Checks.run

-- Complete selected dense forward execution and conditional stored-word accuracy.
#print axioms Ptx.Scalar.Parallel.Dense.leftIndex
#print axioms Ptx.Scalar.Parallel.Dense.nextIndex
#print axioms Ptx.Scalar.Parallel.Dense.round_indices
#print axioms Ptx.Scalar.Parallel.Dense.round_regular
#print axioms Ptx.Scalar.Parallel.Dense.roundFinish
#print axioms Ptx.Scalar.Parallel.Dense.round_effect
#print axioms Ptx.Scalar.Parallel.Dense.program_round_split
#print axioms Ptx.Scalar.Parallel.Dense.round_fetch
#print axioms Ptx.Scalar.Parallel.Dense.round_run
#print axioms Ptx.Scalar.Parallel.Dense.PlaneReady
#print axioms Ptx.Scalar.Parallel.Dense.thread_coordinates
#print axioms Ptx.Scalar.Parallel.Dense.RoundInvariant
#print axioms Ptx.Scalar.Parallel.Dense.round_reads
#print axioms Ptx.Scalar.Parallel.Dense.round_invariant_step
#print axioms Ptx.Scalar.Parallel.Dense.round_phase_exists
#print axioms Ptx.Scalar.Parallel.Dense.first_plane_exists
#print axioms Ptx.Scalar.Parallel.Dense.reduction_exists
#print axioms Ptx.Scalar.Parallel.Dense.rootIndex
#print axioms Ptx.Scalar.Parallel.Dense.biasIndex
#print axioms Ptx.Scalar.Parallel.Dense.outputIndex
#print axioms Ptx.Scalar.Parallel.Dense.output_indices
#print axioms Ptx.Scalar.Parallel.Dense.outputFinish
#print axioms Ptx.Scalar.Parallel.Dense.outputValue
#print axioms Ptx.Scalar.Parallel.Dense.output_regular
#print axioms Ptx.Scalar.Parallel.Dense.output_effect
#print axioms Ptx.Scalar.Parallel.Dense.outputDone
#print axioms Ptx.Scalar.Parallel.Dense.output_fetch
#print axioms Ptx.Scalar.Parallel.Dense.output_run
#print axioms Ptx.Scalar.Parallel.Dense.OutputInvariant
#print axioms Ptx.Scalar.Parallel.Dense.output_value
#print axioms Ptx.Scalar.Parallel.Dense.output_invariant_step
#print axioms Ptx.Scalar.Parallel.Dense.output_phase_exists
#print axioms Ptx.Scalar.Parallel.Dense.selected_forward_exists
#print axioms Ptx.Scalar.Parallel.Dense.selected_forward_accuracy
#print axioms Ptx.Scalar.Parallel.Dense.product_coordinates

-- Concrete-read witnesses, checked replay and actual read origins.
#print axioms Ptx.Scalar.Parallel.ConcreteRuns
#print axioms Ptx.Scalar.Parallel.ConcreteRuns.toRuns
#print axioms Ptx.Scalar.Parallel.concrete_runs_append
#print axioms Ptx.Scalar.Parallel.Replay.Arrays
#print axioms Ptx.Scalar.Parallel.Replay.arrays
#print axioms Ptx.Scalar.Parallel.Replay.effect
#print axioms Ptx.Scalar.Parallel.Replay.event
#print axioms Ptx.Scalar.Parallel.Replay.trace
#print axioms Ptx.Scalar.Parallel.Replay.trace_append
#print axioms Ptx.Scalar.Parallel.Replay.eval_replays
#print axioms Ptx.Scalar.Parallel.Replay.scalar_replays
#print axioms Ptx.Scalar.Parallel.Replay.barriers_replay
#print axioms Ptx.Scalar.Parallel.Replay.dispatch_replays
#print axioms Ptx.Scalar.Parallel.Replay.step_replays
#print axioms Ptx.Scalar.Parallel.Replay.concrete_replays
#print axioms Ptx.Scalar.Parallel.Replay.reject_wrong_load
#print axioms Ptx.Scalar.Parallel.Replay.arena
#print axioms Ptx.Scalar.Parallel.Replay.writtenAt
#print axioms Ptx.Scalar.Parallel.Replay.latestWrite
#print axioms Ptx.Scalar.Parallel.Replay.latestWrite_none
#print axioms Ptx.Scalar.Parallel.Replay.latestWrite_origin
#print axioms Ptx.Scalar.Parallel.Replay.event_value
#print axioms Ptx.Scalar.Parallel.Replay.trace_value
#print axioms Ptx.Scalar.Parallel.Replay.load_prefix
#print axioms Ptx.Scalar.Parallel.Replay.load_source
#print axioms Ptx.Scalar.Parallel.Replay.ReadOrigins
#print axioms Ptx.Scalar.Parallel.Replay.read_origins
#print axioms Ptx.Scalar.Parallel.Replay.writtenAt_some
#print axioms Ptx.Scalar.Parallel.Dense.selected_forward_checked
#print axioms Ptx.Scalar.Parallel.barrier_round_concrete
#print axioms Ptx.Scalar.Parallel.ConcreteSegment
#print axioms Ptx.Scalar.Parallel.ConcreteSegment.toSegment
#print axioms Ptx.Scalar.Parallel.ConcreteSegment.frame
#print axioms Ptx.Scalar.Parallel.ConcreteSegment.append
#print axioms Ptx.Scalar.Parallel.ConcreteSegment.compile
#print axioms Ptx.Scalar.Parallel.segmentReference_concrete
#print axioms Ptx.Scalar.Parallel.Dense.selected_forward_concrete

-- Chronological graph construction and admitted dense forward execution.
#print axioms Ptx.Scalar.Parallel.Memory.Chronology.rank
#print axioms Ptx.Scalar.Parallel.Memory.Chronology.program_origin
#print axioms Ptx.Scalar.Parallel.Memory.Chronology.initial_origin
#print axioms Ptx.Scalar.Parallel.Memory.Chronology.initial_bound
#print axioms Ptx.Scalar.Parallel.Memory.Chronology.initial_rank
#print axioms Ptx.Scalar.Parallel.Memory.Chronology.program_same_position
#print axioms Ptx.Scalar.Parallel.Memory.Chronology.rank_injective
#print axioms Ptx.Scalar.Parallel.Memory.Chronology.program_before
#print axioms Ptx.Scalar.Parallel.Memory.Chronology.initial_iff
#print axioms Ptx.Scalar.Parallel.Memory.Chronology.no_release
#print axioms Ptx.Scalar.Parallel.Memory.Chronology.initial_position
#print axioms Ptx.Scalar.Parallel.Memory.Chronology.initial_before
#print axioms Ptx.Scalar.Parallel.Memory.Chronology.base_before
#print axioms Ptx.Scalar.Parallel.Memory.Chronology.split_at
#print axioms Ptx.Scalar.Parallel.Memory.Chronology.initial_member
#print axioms Ptx.Scalar.Parallel.Memory.Chronology.initial_graph_member
#print axioms Ptx.Scalar.Parallel.Memory.Chronology.writtenAt_of_address
#print axioms Ptx.Scalar.Parallel.Memory.Chronology.SourceFor
#print axioms Ptx.Scalar.Parallel.Memory.Chronology.source_exists
#print axioms Ptx.Scalar.Parallel.Memory.Chronology.chosenSource
#print axioms Ptx.Scalar.Parallel.Memory.Chronology.chronologicalCoherence
#print axioms Ptx.Scalar.Parallel.Memory.Chronology.chosenSource_spec
#print axioms Ptx.Scalar.Parallel.Memory.Chronology.concrete_certificate
#print axioms Ptx.Scalar.Parallel.Memory.Chronology.concrete_admitted
#print axioms Ptx.Scalar.Parallel.Dense.selected_forward_admitted

-- Zero padding and the admitted forward connection to the actual tensor graph.
#print axioms Ptx.Binary32.Reduction.zeroInput
#print axioms Ptx.Binary32.Reduction.paddedInput
#print axioms Ptx.Binary32.Reduction.map_balanced
#print axioms Ptx.Binary32.Reduction.balanced_ideal
#print axioms Ptx.Binary32.Reduction.padded_ideal
#print axioms PtxTorchLean.DenseForward.Encoding
#print axioms PtxTorchLean.DenseForward.Encoding.row
#print axioms PtxTorchLean.DenseForward.Encoding.row_words
#print axioms PtxTorchLean.DenseForward.Encoding.row_ideal
#print axioms PtxTorchLean.DenseForward.forward_word_accuracy
#print axioms PtxTorchLean.DenseForward.selected_forward

-- Arbitrary candidate control order, actual completion timing and dense store sites.
#print axioms Ptx.Scalar.Parallel.Control.StraightOp
#print axioms Ptx.Scalar.Parallel.Control.StraightInstr
#print axioms Ptx.Scalar.Parallel.Control.Straight
#print axioms Ptx.Scalar.Parallel.Control.stamp
#print axioms Ptx.Scalar.Parallel.Control.cursor
#print axioms Ptx.Scalar.Parallel.Control.cursor_bounds
#print axioms Ptx.Scalar.Parallel.Control.Progress
#print axioms Ptx.Scalar.Parallel.Control.dispatch_progress
#print axioms Ptx.Scalar.Parallel.Control.step_progress
#print axioms Ptx.Scalar.Parallel.Control.TraceProgress
#print axioms Ptx.Scalar.Parallel.Control.runs_progress
#print axioms Ptx.Scalar.Parallel.Control.same_site_unique
#print axioms Ptx.Scalar.Parallel.Control.position_iff_pc
#print axioms Ptx.Scalar.Parallel.Control.dispatch_completion
#print axioms Ptx.Scalar.Parallel.Control.step_completion
#print axioms Ptx.Scalar.Parallel.Control.completion_split
#print axioms Ptx.Scalar.Parallel.Control.completion_orders_sites
#print axioms Ptx.Scalar.Parallel.Control.site_after_completion
#print axioms Ptx.Scalar.Parallel.Control.completed_sites_ordered
#print axioms Ptx.Scalar.Parallel.Control.completion_site_unique
#print axioms Ptx.Scalar.Parallel.Memory.run_read_from_unique_writer_sites
#print axioms Ptx.Scalar.Parallel.Dense.program_straight
#print axioms Ptx.Scalar.Parallel.Dense.scalar_site_unique
#print axioms Ptx.Scalar.Parallel.Dense.scalar_before_arrival
#print axioms Ptx.Scalar.Parallel.Dense.scalar_after_completion
#print axioms Ptx.Scalar.Parallel.Dense.fetched_store_site
#print axioms Ptx.Scalar.Parallel.Dense.trace_store_site

-- Computed-address ownership for arbitrary candidate dense forward traces.
#print axioms Ptx.Scalar.Parallel.AddressControl.Visible
#print axioms Ptx.Scalar.Parallel.AddressControl.Agree
#print axioms Ptx.Scalar.Parallel.AddressControl.advance
#print axioms Ptx.Scalar.Parallel.AddressControl.scalar
#print axioms Ptx.Scalar.Parallel.AddressControl.instruction
#print axioms Ptx.Scalar.Parallel.AddressControl.Known
#print axioms Ptx.Scalar.Parallel.AddressControl.Allowed
#print axioms Ptx.Scalar.Parallel.AddressControl.Compatible
#print axioms Ptx.Scalar.Parallel.AddressControl.ProgramCompatible
#print axioms Ptx.Scalar.Parallel.AddressControl.agree_refl
#print axioms Ptx.Scalar.Parallel.AddressControl.agree_advance
#print axioms Ptx.Scalar.Parallel.AddressControl.agree_word
#print axioms Ptx.Scalar.Parallel.AddressControl.agree_word_left
#print axioms Ptx.Scalar.Parallel.AddressControl.agree_word_right
#print axioms Ptx.Scalar.Parallel.AddressControl.agree_address
#print axioms Ptx.Scalar.Parallel.AddressControl.agree_predicate
#print axioms Ptx.Scalar.Parallel.AddressControl.agree_predicate_right
#print axioms Ptx.Scalar.Parallel.AddressControl.operand32_eq
#print axioms Ptx.Scalar.Parallel.AddressControl.operand64_eq
#print axioms Ptx.Scalar.Parallel.AddressControl.scalar_agrees
#print axioms Ptx.Scalar.Parallel.AddressControl.evaluate
#print axioms Ptx.Scalar.Parallel.AddressControl.atPC
#print axioms Ptx.Scalar.Parallel.AddressControl.evaluate_append
#print axioms Ptx.Scalar.Parallel.AddressControl.atPC_succ
#print axioms Ptx.Scalar.Parallel.AddressControl.scalar_pc
#print axioms Ptx.Scalar.Parallel.AddressControl.Invariant
#print axioms Ptx.Scalar.Parallel.AddressControl.dispatch_invariant
#print axioms Ptx.Scalar.Parallel.AddressControl.step_invariant
#print axioms Ptx.Scalar.Parallel.AddressControl.runs_invariant
#print axioms Ptx.Scalar.Parallel.AddressControl.step_store
#print axioms Ptx.Scalar.Parallel.AddressControl.run_store
#print axioms Ptx.Scalar.Parallel.Dense.program_address_compatible
#print axioms Ptx.Scalar.Parallel.Dense.controlSeed
#print axioms Ptx.Scalar.Parallel.Dense.initial_address_control
#print axioms Ptx.Scalar.Parallel.Dense.candidate_address_control
#print axioms Ptx.Scalar.Parallel.Dense.ControlCoordinates
#print axioms Ptx.Scalar.Parallel.Dense.products_control_coordinates
#print axioms Ptx.Scalar.Parallel.Dense.round_control_coordinates
#print axioms Ptx.Scalar.Parallel.Dense.rounds_control_coordinates
#print axioms Ptx.Scalar.Parallel.Dense.product_control_address
#print axioms Ptx.Scalar.Parallel.Dense.round_control_address
#print axioms Ptx.Scalar.Parallel.Dense.output_control_address
#print axioms Ptx.Scalar.Parallel.Dense.candidate_store_address
#print axioms Ptx.Scalar.Parallel.Dense.sharedStorePC
#print axioms Ptx.Scalar.Parallel.Dense.candidate_shared_owner
#print axioms Ptx.Scalar.Parallel.Dense.candidate_global_owner
#print axioms Ptx.Scalar.Parallel.Dense.shared_store_unique
#print axioms Ptx.Scalar.Parallel.Dense.global_store_unique
#print axioms Ptx.Scalar.Parallel.Dense.candidate_store_unique
#print axioms Ptx.Scalar.Parallel.Dense.graph_writer_unique

-- Actual producers and barrier completions in arbitrary finished dense executions.
#print axioms Ptx.Scalar.Parallel.Dense.control_atPC_slice
#print axioms Ptx.Scalar.Parallel.Dense.round_control_active
#print axioms Ptx.Scalar.Parallel.Control.dispatch_pc_bound
#print axioms Ptx.Scalar.Parallel.Control.step_pc_bound
#print axioms Ptx.Scalar.Parallel.Control.crossing_step
#print axioms Ptx.Scalar.Parallel.Control.memory_crossing
#print axioms Ptx.Scalar.Parallel.Control.barrier_crossing
#print axioms Ptx.Scalar.Parallel.Control.crossed_barrier_exists
#print axioms Ptx.Scalar.Parallel.Control.halted_exit_origin
#print axioms Ptx.Scalar.Parallel.Dense.fetched_exit_site
#print axioms Ptx.Scalar.Parallel.Dense.completed_pc_bound
#print axioms Ptx.Scalar.Parallel.Dense.completed_barrier_exists
#print axioms Ptx.Scalar.Parallel.Dense.completed_phases
#print axioms Ptx.Scalar.Parallel.Dense.completed_product_store
#print axioms Ptx.Scalar.Parallel.Dense.completed_round_store
#print axioms Ptx.Scalar.Parallel.Dense.completed_output_store
#print axioms Ptx.Scalar.Parallel.Dense.completed_product_publication
#print axioms Ptx.Scalar.Parallel.Dense.completed_round_publication

-- Universal completed dense forward execution, forced sources, and no-launch wrapper.
#print axioms Ptx.Scalar.Parallel.Dense.Node
#print axioms Ptx.Scalar.Parallel.Dense.Output
#print axioms Ptx.Scalar.Parallel.Dense.node_leaf
#print axioms Ptx.Scalar.Parallel.Dense.node_fork
#print axioms Ptx.Scalar.Parallel.Dense.Data
#print axioms Ptx.Scalar.Parallel.Dense.ReadData
#print axioms Ptx.Scalar.Parallel.Dense.StoreData
#print axioms Ptx.Scalar.Parallel.Dense.initial_data
#print axioms Ptx.Scalar.Parallel.Dense.product_fp_data
#print axioms Ptx.Scalar.Parallel.Dense.round_fp_data
#print axioms Ptx.Scalar.Parallel.Dense.output_fp_data
#print axioms Ptx.Scalar.Parallel.Dense.DataInvariant
#print axioms Ptx.Scalar.Parallel.Dense.Stores
#print axioms Ptx.Scalar.Parallel.Dense.Reads
#print axioms Ptx.Scalar.Parallel.Dense.dispatch_data
#print axioms Ptx.Scalar.Parallel.Dense.step_data
#print axioms Ptx.Scalar.Parallel.Dense.scalar_step_singleton
#print axioms Ptx.Scalar.Parallel.Dense.program_segment
#print axioms Ptx.Scalar.Parallel.Dense.scalar_data
#print axioms Ptx.Scalar.Parallel.Dense.fp_data
#print axioms Ptx.Scalar.Parallel.Dense.barrier_data
#print axioms Ptx.Scalar.Parallel.Dense.run_data
#print axioms Ptx.Scalar.Parallel.Dense.product_scalar_data
#print axioms Ptx.Scalar.Parallel.Dense.round_scalar_data
#print axioms Ptx.Scalar.Parallel.Dense.output_scalar_data
#print axioms Ptx.Scalar.Parallel.Dense.global_load_index
#print axioms Ptx.Scalar.Parallel.Dense.global_prefix_unwritten
#print axioms Ptx.Scalar.Parallel.Dense.global_read_source
#print axioms Ptx.Scalar.Parallel.Dense.launchPlan
#print axioms Ptx.Scalar.Parallel.Dense.launchPlan_empty
#print axioms Ptx.Scalar.Parallel.Dense.launchPlan_kernel
#print axioms Ptx.Scalar.Parallel.Dense.ForwardRun
#print axioms Ptx.Scalar.Parallel.Dense.empty_forward
#print axioms Ptx.Scalar.Parallel.Dense.empty_forward_unique
#print axioms Ptx.Scalar.Parallel.Dense.product_read_control
#print axioms Ptx.Scalar.Parallel.Dense.round_read_control
#print axioms Ptx.Scalar.Parallel.Dense.output_read_control
#print axioms Ptx.Scalar.Parallel.Dense.productLoad
#print axioms Ptx.Scalar.Parallel.Dense.roundLoad
#print axioms Ptx.Scalar.Parallel.Dense.outputLoad
#print axioms Ptx.Scalar.Parallel.Dense.fetched_load_site
#print axioms Ptx.Scalar.Parallel.Dense.candidate_load_address
#print axioms Ptx.Scalar.Parallel.Dense.scratch_pointer_owner
#print axioms Ptx.Scalar.Parallel.Dense.store_node
#print axioms Ptx.Scalar.Parallel.Dense.shared_load_node
#print axioms Ptx.Scalar.Parallel.Dense.read_data
#print axioms Ptx.Scalar.Parallel.Dense.Admitted
#print axioms Ptx.Scalar.Parallel.Dense.visible_store
#print axioms Ptx.Scalar.Parallel.Dense.plane_publication
#print axioms Ptx.Scalar.Parallel.Dense.child_owner
#print axioms Ptx.Scalar.Parallel.Dense.shared_read_source
#print axioms Ptx.Scalar.Parallel.Dense.scalar_store_data
#print axioms Ptx.Scalar.Parallel.Dense.completed_forward
#print axioms Ptx.Scalar.Parallel.AddressControl.step_load
#print axioms Ptx.Scalar.Parallel.AddressControl.run_load
#print axioms Ptx.Scalar.Parallel.Replay.latestWrite_append
#print axioms Ptx.Scalar.Parallel.Replay.run_value
#print axioms PtxTorchLean.DenseForward.output_accuracy
#print axioms PtxTorchLean.DenseForward.universal_forward
#print axioms PtxTorchLean.DenseForward.wrapper_forward

-- Completed parallel dense backward: stored handoffs, universal accuracy, and existence.
#print axioms Ptx.Scalar.Parallel.DenseBackward.Checks.run
#print axioms Ptx.Scalar.Parallel.DenseBackward.Shape
#print axioms Ptx.Scalar.Parallel.DenseBackward.Shape.transposed
#print axioms Ptx.Scalar.Parallel.DenseBackward.Shape.gateBase
#print axioms Ptx.Scalar.Parallel.DenseBackward.Shape.weightBase
#print axioms Ptx.Scalar.Parallel.DenseBackward.Shape.weightCount
#print axioms Ptx.Scalar.Parallel.DenseBackward.Shape.copyBase
#print axioms Ptx.Scalar.Parallel.DenseBackward.Bounds
#print axioms Ptx.Scalar.Parallel.DenseBackward.gateLayout
#print axioms Ptx.Scalar.Parallel.DenseBackward.weightLayout
#print axioms Ptx.Scalar.Parallel.DenseBackward.copySource
#print axioms Ptx.Scalar.Parallel.DenseBackward.copy_source_bound
#print axioms Ptx.Scalar.Parallel.DenseBackward.copyLayout
#print axioms Ptx.Scalar.Parallel.DenseBackward.gateInput
#print axioms Ptx.Scalar.Parallel.DenseBackward.weightInput
#print axioms Ptx.Scalar.Parallel.DenseBackward.copyInput
#print axioms Ptx.Scalar.Parallel.DenseBackward.packet
#print axioms Ptx.Scalar.Parallel.DenseBackward.Execution
#print axioms Ptx.Scalar.Parallel.DenseBackward.execution_exists
#print axioms Ptx.Scalar.Parallel.DenseBackward.Execution.g
#print axioms Ptx.Scalar.Parallel.DenseBackward.Execution.dw
#print axioms Ptx.Scalar.Parallel.DenseBackward.Execution.dx
#print axioms Ptx.Scalar.Parallel.DenseBackward.lengths
#print axioms Ptx.Scalar.Parallel.DenseBackward.input_frame
#print axioms Ptx.Scalar.Parallel.DenseBackward.gate_frame
#print axioms Ptx.Scalar.Parallel.DenseBackward.gate_result
#print axioms Ptx.Scalar.Parallel.DenseBackward.weight_result
#print axioms Ptx.Scalar.Parallel.DenseBackward.packet_word
#print axioms Ptx.Scalar.Parallel.DenseBackward.packet_input
#print axioms Ptx.Scalar.Parallel.DenseBackward.packet_weight
#print axioms Ptx.Scalar.Parallel.DenseBackward.packet_bias
#print axioms Ptx.Scalar.Parallel.DenseBackward.input_result
#print axioms Ptx.Scalar.Parallel.DenseBackward.gradients_stored
#print axioms Ptx.Scalar.Parallel.Dense.Launch
#print axioms Ptx.Scalar.Parallel.Dense.launch_exists
#print axioms Ptx.Scalar.Parallel.Dense.launch_correct
#print axioms Ptx.Scalar.Parallel.Dense.activate
#print axioms Ptx.Scalar.Parallel.Dense.activateReal
#print axioms Ptx.Scalar.Parallel.Pointwise.compatible
#print axioms Ptx.Scalar.Parallel.Pointwise.control_addresses
#print axioms Ptx.Scalar.Parallel.Pointwise.initial_control
#print axioms Ptx.Scalar.Parallel.Pointwise.initial_aligned
#print axioms Ptx.Scalar.Parallel.Pointwise.fetched_load
#print axioms Ptx.Scalar.Parallel.Pointwise.fetched_store
#print axioms Ptx.Scalar.Parallel.Pointwise.load_address
#print axioms Ptx.Scalar.Parallel.Pointwise.store_address
#print axioms Ptx.Scalar.Parallel.Pointwise.RegisterValue
#print axioms Ptx.Scalar.Parallel.Pointwise.Data
#print axioms Ptx.Scalar.Parallel.Pointwise.gate_bits
#print axioms Ptx.Scalar.Parallel.Pointwise.scalar_data
#print axioms Ptx.Scalar.Parallel.Pointwise.fp_data
#print axioms Ptx.Scalar.Parallel.Pointwise.scalar_store_data
#print axioms Ptx.Scalar.Parallel.Pointwise.Pointers
#print axioms Ptx.Scalar.Parallel.Pointwise.finish
#print axioms Ptx.Scalar.Parallel.Pointwise.lane_regular
#print axioms Ptx.Scalar.Parallel.Pointwise.lane_effect
#print axioms Ptx.Scalar.Parallel.Pointwise.done
#print axioms Ptx.Scalar.Parallel.Pointwise.lane_run
#print axioms Ptx.Scalar.Parallel.Pointwise.Progress
#print axioms Ptx.Scalar.Parallel.Pointwise.execution_exists
#print axioms Ptx.Scalar.Parallel.Pointwise.admitted_exists
#print axioms Ptx.Scalar.Parallel.Pointwise.Launch
#print axioms Ptx.Scalar.Parallel.Pointwise.launch_exists
#print axioms Ptx.Scalar.Parallel.Pointwise.launch_correct
#print axioms Ptx.Scalar.Parallel.Pointwise.launch_access_safe
#print axioms Ptx.Scalar.Parallel.Pointwise.DataInvariant
#print axioms Ptx.Scalar.Parallel.Pointwise.Stores
#print axioms Ptx.Scalar.Parallel.Pointwise.Reads
#print axioms Ptx.Scalar.Parallel.Pointwise.dispatch_data
#print axioms Ptx.Scalar.Parallel.Pointwise.step_data
#print axioms Ptx.Scalar.Parallel.Pointwise.scalar_step_singleton
#print axioms Ptx.Scalar.Parallel.Pointwise.Op
#print axioms Ptx.Scalar.Parallel.Pointwise.localOp
#print axioms Ptx.Scalar.Parallel.Pointwise.clear
#print axioms Ptx.Scalar.Parallel.Pointwise.body
#print axioms Ptx.Scalar.Parallel.Pointwise.program
#print axioms Ptx.Scalar.Parallel.Pointwise.storePC
#print axioms Ptx.Scalar.Parallel.Pointwise.Result
#print axioms Ptx.Scalar.Parallel.Pointwise.reference
#print axioms Ptx.Scalar.Parallel.Pointwise.reference_result
#print axioms Ptx.Scalar.Parallel.Pointwise.Layout
#print axioms Ptx.Scalar.Parallel.Pointwise.Layout.output
#print axioms Ptx.Scalar.Parallel.Pointwise.seed
#print axioms Ptx.Scalar.Parallel.Pointwise.initial
#print axioms Ptx.Scalar.Parallel.Pointwise.config
#print axioms Ptx.Scalar.Parallel.Pointwise.length_program
#print axioms Ptx.Scalar.Parallel.Pointwise.straight
#print axioms Ptx.Scalar.Parallel.Pointwise.Admitted
#print axioms Ptx.Scalar.Parallel.Pointwise.pointer_index
#print axioms Ptx.Scalar.Parallel.Pointwise.prefix_unwritten
#print axioms Ptx.Scalar.Parallel.Pointwise.read_source
#print axioms Ptx.Scalar.Parallel.Pointwise.run_data
#print axioms Ptx.Scalar.Parallel.Pointwise.completed_pc
#print axioms Ptx.Scalar.Parallel.Pointwise.completed_store
#print axioms Ptx.Scalar.Parallel.Pointwise.written_result
#print axioms Ptx.Scalar.Parallel.Pointwise.completed
#print axioms PtxTorchLean.DenseBackward.Encoding
#print axioms PtxTorchLean.DenseBackward.Encoding.gWord
#print axioms PtxTorchLean.DenseBackward.Encoding.gReal
#print axioms PtxTorchLean.DenseBackward.Encoding.gIdeal
#print axioms PtxTorchLean.DenseBackward.Encoding.g_real
#print axioms PtxTorchLean.DenseBackward.Encoding.affine_accuracy
#print axioms PtxTorchLean.DenseBackward.Encoding.g_error
#print axioms PtxTorchLean.DenseBackward.Encoding.g_ideal
#print axioms PtxTorchLean.DenseBackward.stored_gate
#print axioms PtxTorchLean.DenseBackward.ProductRanges
#print axioms PtxTorchLean.DenseBackward.weightEntry
#print axioms PtxTorchLean.DenseBackward.inputEntry
#print axioms PtxTorchLean.DenseBackward.inputTree
#print axioms PtxTorchLean.DenseBackward.Ranges
#print axioms PtxTorchLean.DenseBackward.inputRow
#print axioms PtxTorchLean.DenseBackward.input_words
#print axioms PtxTorchLean.DenseBackward.input_ideal
#print axioms PtxTorchLean.DenseBackward.weight_accuracy
#print axioms PtxTorchLean.DenseBackward.input_accuracy
#print axioms PtxTorchLean.DenseBackward.bias_accuracy
#print axioms PtxTorchLean.DenseBackward.Encoding.away
#print axioms PtxTorchLean.DenseBackward.Correct
#print axioms PtxTorchLean.DenseBackward.universal_backward
#print axioms PtxTorchLean.DenseBackward.backward_exists

-- Actual grid execution, pointwise existence, and conditional universal dense forward.
#print axioms Ptx.Scalar.Parallel.Dense.ArithmeticBounds
#print axioms Ptx.Scalar.Parallel.Grid.step_memory_origin
#print axioms Ptx.Scalar.Parallel.Grid.run_memory_origin
#print axioms Ptx.Scalar.Parallel.Grid.run_store
#print axioms Ptx.Scalar.Parallel.Grid.run_load
#print axioms Ptx.Scalar.Parallel.Grid.project_mem
#print axioms Ptx.Scalar.Parallel.Grid.completed_arrival
#print axioms Ptx.Scalar.Parallel.Grid.Checks.run
#print axioms Ptx.Scalar.Parallel.Grid.Control.step_completion
#print axioms Ptx.Scalar.Parallel.Grid.Control.completion_split
#print axioms Ptx.Scalar.Parallel.Grid.Control.completion_orders_sites
#print axioms Ptx.Scalar.Parallel.Grid.Control.site_after_completion
#print axioms Ptx.Scalar.Parallel.Grid.Control.completed_sites_ordered
#print axioms Ptx.Scalar.Parallel.Grid.Control.completion_site_unique
#print axioms Ptx.Scalar.Parallel.Grid.Control.stamp
#print axioms Ptx.Scalar.Parallel.Grid.Control.cursor
#print axioms Ptx.Scalar.Parallel.Grid.Control.cursor_bounds
#print axioms Ptx.Scalar.Parallel.Grid.Control.Progress
#print axioms Ptx.Scalar.Parallel.Grid.Control.step_progress
#print axioms Ptx.Scalar.Parallel.Grid.Control.TraceProgress
#print axioms Ptx.Scalar.Parallel.Grid.Control.runs_progress
#print axioms Ptx.Scalar.Parallel.Grid.Control.same_site_unique
#print axioms Ptx.Scalar.Parallel.Grid.Control.position_iff_pc
#print axioms Ptx.Scalar.Parallel.Grid.Control.step_pc_bound
#print axioms Ptx.Scalar.Parallel.Grid.Control.crossing_step
#print axioms Ptx.Scalar.Parallel.Grid.Control.crossed_barrier_exists
#print axioms Ptx.Scalar.Parallel.Grid.Control.halted_exit_origin
#print axioms Ptx.Scalar.Parallel.GridDense.candidate_store_address
#print axioms Ptx.Scalar.Parallel.GridDense.candidate_load_address
#print axioms Ptx.Scalar.Parallel.GridDense.Checks.check
#print axioms Ptx.Scalar.Parallel.GridDense.Checks.run
#print axioms Ptx.Scalar.Parallel.GridDense.Phase
#print axioms Ptx.Scalar.Parallel.GridDense.completed_pc_bound
#print axioms Ptx.Scalar.Parallel.GridDense.completed_barrier_exists
#print axioms Ptx.Scalar.Parallel.GridDense.completed_phases
#print axioms Ptx.Scalar.Parallel.GridDense.completed_product_store
#print axioms Ptx.Scalar.Parallel.GridDense.completed_round_store
#print axioms Ptx.Scalar.Parallel.GridDense.completed_output_store
#print axioms Ptx.Scalar.Parallel.GridDense.LocalData.DataInvariant
#print axioms Ptx.Scalar.Parallel.GridDense.LocalData.Stores
#print axioms Ptx.Scalar.Parallel.GridDense.LocalData.Reads
#print axioms Ptx.Scalar.Parallel.GridDense.LocalData.dispatch_data
#print axioms Ptx.Scalar.Parallel.GridDense.LocalData.step_data
#print axioms Ptx.Scalar.Parallel.GridDense.DataInvariant
#print axioms Ptx.Scalar.Parallel.GridDense.Stores
#print axioms Ptx.Scalar.Parallel.GridDense.Reads
#print axioms Ptx.Scalar.Parallel.GridDense.step_data
#print axioms Ptx.Scalar.Parallel.GridDense.scalar_step_singleton
#print axioms Ptx.Scalar.Parallel.GridDense.run_data
#print axioms Ptx.Scalar.Parallel.GridDense.global_load_index
#print axioms Ptx.Scalar.Parallel.GridDense.global_prefix_unwritten
#print axioms Ptx.Scalar.Parallel.GridDense.global_read_source
#print axioms Ptx.Scalar.Parallel.GridDense.candidate_shared_owner
#print axioms Ptx.Scalar.Parallel.GridDense.candidate_global_owner
#print axioms Ptx.Scalar.Parallel.GridDense.scalar_site_unique
#print axioms Ptx.Scalar.Parallel.GridDense.shared_store_unique
#print axioms Ptx.Scalar.Parallel.GridDense.global_store_unique
#print axioms Ptx.Scalar.Parallel.GridDense.Bounds
#print axioms Ptx.Scalar.Parallel.GridDense.config
#print axioms Ptx.Scalar.Parallel.GridDense.thread
#print axioms Ptx.Scalar.Parallel.GridDense.initial
#print axioms Ptx.Scalar.Parallel.GridDense.thread_coordinates
#print axioms Ptx.Scalar.Parallel.GridDense.thread_unique
#print axioms Ptx.Scalar.Parallel.GridDense.initial_aligned
#print axioms Ptx.Scalar.Parallel.GridDense.initial_control
#print axioms Ptx.Scalar.Parallel.GridDense.candidate_control
#print axioms Ptx.Scalar.Parallel.GridDense.scratch_pointer_owner
#print axioms Ptx.Scalar.Parallel.GridDense.store_node
#print axioms Ptx.Scalar.Parallel.GridDense.shared_load_node
#print axioms Ptx.Scalar.Parallel.GridDense.read_data
#print axioms Ptx.Scalar.Parallel.GridDense.Admitted
#print axioms Ptx.Scalar.Parallel.GridDense.visible_store
#print axioms Ptx.Scalar.Parallel.GridDense.plane_publication
#print axioms Ptx.Scalar.Parallel.GridDense.child_owner
#print axioms Ptx.Scalar.Parallel.GridDense.shared_read_source
#print axioms Ptx.Scalar.Parallel.GridDense.completed_forward
#print axioms Ptx.Scalar.Parallel.GridDense.candidate_store_unique
#print axioms Ptx.Scalar.Parallel.GridDense.graph_writer_unique
#print axioms Ptx.Scalar.Parallel.Grid.Local
#print axioms Ptx.Scalar.Parallel.Grid.State
#print axioms Ptx.Scalar.Parallel.Grid.Config
#print axioms Ptx.Scalar.Parallel.Grid.Config.group
#print axioms Ptx.Scalar.Parallel.Grid.view
#print axioms Ptx.Scalar.Parallel.Grid.localOf
#print axioms Ptx.Scalar.Parallel.Grid.install
#print axioms Ptx.Scalar.Parallel.Grid.tag
#print axioms Ptx.Scalar.Parallel.Grid.Step
#print axioms Ptx.Scalar.Parallel.Grid.Runs
#print axioms Ptx.Scalar.Parallel.Grid.view_install_same
#print axioms Ptx.Scalar.Parallel.Grid.install_local_other
#print axioms Ptx.Scalar.Parallel.Grid.view_install_other
#print axioms Ptx.Scalar.Parallel.Grid.step_exists
#print axioms Ptx.Scalar.Parallel.Grid.step_lengths
#print axioms Ptx.Scalar.Parallel.Grid.runs_lengths
#print axioms Ptx.Scalar.Parallel.Grid.AccessSafe
#print axioms Ptx.Scalar.Parallel.Grid.step_access_safe
#print axioms Ptx.Scalar.Parallel.Grid.access_safe_of_lengths
#print axioms Ptx.Scalar.Parallel.Grid.runs_access_safe
#print axioms Ptx.Scalar.Parallel.Grid.step_aligned
#print axioms Ptx.Scalar.Parallel.Grid.runs_aligned
#print axioms Ptx.Scalar.Parallel.Grid.runs_append
#print axioms Ptx.Scalar.Parallel.Grid.embed_run
#print axioms Ptx.Scalar.Parallel.Grid.flatThread
#print axioms Ptx.Scalar.Parallel.Grid.product_div
#print axioms Ptx.Scalar.Parallel.Grid.product_mod
#print axioms Ptx.Scalar.Parallel.Grid.flatten
#print axioms Ptx.Scalar.Parallel.Grid.flatEvent
#print axioms Ptx.Scalar.Parallel.Grid.flatEvents
#print axioms Ptx.Scalar.Parallel.Grid.flatten_global
#print axioms Ptx.Scalar.Parallel.Grid.view_global
#print axioms Ptx.Scalar.Parallel.Grid.view_lanes
#print axioms Ptx.Scalar.Parallel.Grid.flatten_lane
#print axioms Ptx.Scalar.Parallel.Grid.install_view
#print axioms Ptx.Scalar.Parallel.Grid.flatten_install_lane
#print axioms Ptx.Scalar.Parallel.Grid.GlobalOnly
#print axioms Ptx.Scalar.Parallel.Grid.IdleBarriers
#print axioms Ptx.Scalar.Parallel.Grid.flatten_install_global
#print axioms Ptx.Scalar.Parallel.Grid.flatOutcome
#print axioms Ptx.Scalar.Parallel.Grid.scalar_flatten
#print axioms Ptx.Scalar.Parallel.Grid.dispatch_flatten
#print axioms Ptx.Scalar.Parallel.Grid.dispatch_barrier
#print axioms Ptx.Scalar.Parallel.Grid.step_barrier
#print axioms Ptx.Scalar.Parallel.Grid.step_idle
#print axioms Ptx.Scalar.Parallel.Grid.local_step_flatten
#print axioms Ptx.Scalar.Parallel.Grid.flatten_run
#print axioms Ptx.Scalar.Parallel.Grid.Memory.threadId
#print axioms Ptx.Scalar.Parallel.Grid.Memory.owner
#print axioms Ptx.Scalar.Parallel.Grid.Memory.ofEffect
#print axioms Ptx.Scalar.Parallel.Grid.Memory.access
#print axioms Ptx.Scalar.Parallel.Grid.Memory.initials
#print axioms Ptx.Scalar.Parallel.Grid.Memory.label
#print axioms Ptx.Scalar.Parallel.Grid.Memory.labels
#print axioms Ptx.Scalar.Parallel.Grid.Memory.graph
#print axioms Ptx.Scalar.Parallel.Grid.Memory.cross
#print axioms Ptx.Scalar.Parallel.Grid.Memory.Admitted
#print axioms Ptx.Scalar.Parallel.Grid.Memory.access_complete
#print axioms Ptx.Scalar.Parallel.Grid.Memory.graph_complete
#print axioms Ptx.Scalar.Parallel.Grid.Memory.threadId_unique
#print axioms Ptx.Scalar.Parallel.Grid.Memory.cross_forward
#print axioms Ptx.Scalar.Parallel.Grid.Memory.access_origin
#print axioms Ptx.Scalar.Parallel.Grid.Memory.labels_origin
#print axioms Ptx.Scalar.Parallel.Grid.Memory.program_write_origin
#print axioms Ptx.Scalar.Parallel.Grid.Memory.initial_origin
#print axioms Ptx.Scalar.Parallel.Grid.Memory.initial_global
#print axioms Ptx.Scalar.Parallel.Grid.Memory.initials_unique
#print axioms Ptx.Scalar.Parallel.Grid.Memory.labels_unique
#print axioms Ptx.Scalar.Parallel.Grid.project
#print axioms Ptx.Scalar.Parallel.Grid.project_append
#print axioms Ptx.Scalar.Parallel.Grid.project_tag_same
#print axioms Ptx.Scalar.Parallel.Grid.project_tag_other
#print axioms Ptx.Scalar.Parallel.Grid.Origins
#print axioms Ptx.Scalar.Parallel.Grid.step_origins
#print axioms Ptx.Scalar.Parallel.Grid.runs_origins
#print axioms Ptx.Scalar.Parallel.Grid.completed_arrivals
#print axioms Ptx.Scalar.Parallel.Grid.Invariant
#print axioms Ptx.Scalar.Parallel.Grid.step_invariant
#print axioms Ptx.Scalar.Parallel.Grid.runs_invariant
#print axioms Ptx.Scalar.Parallel.Grid.runs_address_control
#print axioms Ptx.Scalar.Parallel.Grid.location
#print axioms Ptx.Scalar.Parallel.Grid.shared_private
#print axioms Ptx.Scalar.Parallel.Grid.global_shared_distinct
#print axioms Ptx.Scalar.Parallel.Grid.global_common
#print axioms Ptx.Scalar.Parallel.Grid.latestGlobal
#print axioms Ptx.Scalar.Parallel.Grid.latestGlobal_append
#print axioms Ptx.Scalar.Parallel.Grid.step_global_value
#print axioms Ptx.Scalar.Parallel.Grid.run_global_value
#print axioms Ptx.Scalar.Parallel.Grid.unchanged_global
#print axioms Ptx.Scalar.Parallel.Grid.global_frame
#print axioms Ptx.Scalar.Parallel.GridPointwise.initial
#print axioms Ptx.Scalar.Parallel.GridPointwise.initial_flatten
#print axioms Ptx.Scalar.Parallel.GridPointwise.initial_idle
#print axioms Ptx.Scalar.Parallel.GridPointwise.program_global
#print axioms Ptx.Scalar.Parallel.GridPointwise.candidate_run
#print axioms Ptx.Scalar.Parallel.GridPointwise.Admitted
#print axioms Ptx.Scalar.Parallel.GridPointwise.completed
#print axioms Ptx.Scalar.Parallel.GridPointwise.admitted_exists
#print axioms Ptx.Scalar.Parallel.GridPointwise.Launch
#print axioms Ptx.Scalar.Parallel.GridPointwise.launch_exists
#print axioms Ptx.Scalar.Parallel.GridPointwise.launch_correct
#print axioms Ptx.Scalar.Parallel.GridPointwise.groupCount
#print axioms Ptx.Scalar.Parallel.GridPointwise.capacity_bounds
#print axioms Ptx.Scalar.Parallel.GridPointwise.empty_groupCount
#print axioms Ptx.Scalar.Parallel.GridPointwise.paddedLayout
#print axioms Ptx.Scalar.Parallel.GridPointwise.padded_exists
#print axioms Ptx.Scalar.Parallel.GridPointwise.padded_correct
#print axioms Ptx.Scalar.Parallel.Grid.Reference.step
#print axioms Ptx.Scalar.Parallel.Grid.Reference.run
#print axioms Ptx.Scalar.Parallel.Grid.Reference.step_sound
#print axioms Ptx.Scalar.Parallel.Grid.Reference.run_sound
#print axioms Ptx.Scalar.Parallel.Grid.dispatch_reflect
#print axioms Ptx.Scalar.Parallel.Grid.local_step_reflect
#print axioms Ptx.Scalar.Parallel.Grid.reflect_run
#print axioms PtxTorchLean.GridDenseForward.universal_forward

-- Combined grid admission, complete dense launch existence and five-stage backward.
#print axioms Ptx.Scalar.Parallel.Dense.Local.afterSetup
#print axioms Ptx.Scalar.Parallel.Dense.Local.setup_execution
#print axioms Ptx.Scalar.Parallel.Dense.Local.productFinish
#print axioms Ptx.Scalar.Parallel.Dense.Local.product_segment
#print axioms Ptx.Scalar.Parallel.Dense.Local.round_regular
#print axioms Ptx.Scalar.Parallel.Dense.Local.output_regular
#print axioms Ptx.Scalar.Parallel.Grid.Memory.Chronology.chosenSource
#print axioms Ptx.Scalar.Parallel.Grid.Memory.Chronology.chronologicalCoherence
#print axioms Ptx.Scalar.Parallel.Grid.Memory.Chronology.chosenSource_spec
#print axioms Ptx.Scalar.Parallel.Grid.Memory.Chronology.concrete_certificate
#print axioms Ptx.Scalar.Parallel.Grid.Memory.Chronology.concrete_admitted
#print axioms Ptx.Scalar.Parallel.Grid.Memory.Chronology.concrete_admitted_exists
#print axioms Ptx.Scalar.Parallel.Grid.Memory.Chronology.ceiling
#print axioms Ptx.Scalar.Parallel.Grid.Memory.Chronology.rank
#print axioms Ptx.Scalar.Parallel.Grid.Memory.Chronology.program_origin
#print axioms Ptx.Scalar.Parallel.Grid.Memory.Chronology.initial_origin
#print axioms Ptx.Scalar.Parallel.Grid.Memory.Chronology.initial_bound
#print axioms Ptx.Scalar.Parallel.Grid.Memory.Chronology.initial_rank
#print axioms Ptx.Scalar.Parallel.Grid.Memory.Chronology.program_same_position
#print axioms Ptx.Scalar.Parallel.Grid.Memory.Chronology.rank_injective
#print axioms Ptx.Scalar.Parallel.Grid.Memory.Chronology.program_before
#print axioms Ptx.Scalar.Parallel.Grid.Memory.Chronology.initial_iff
#print axioms Ptx.Scalar.Parallel.Grid.Memory.Chronology.no_release
#print axioms Ptx.Scalar.Parallel.Grid.Memory.Chronology.initial_position
#print axioms Ptx.Scalar.Parallel.Grid.Memory.Chronology.initial_before
#print axioms Ptx.Scalar.Parallel.Grid.Memory.Chronology.base_before
#print axioms Ptx.Scalar.Parallel.Grid.ConcreteRuns
#print axioms Ptx.Scalar.Parallel.Grid.ConcreteRuns.toRuns
#print axioms Ptx.Scalar.Parallel.Grid.concrete_runs_append
#print axioms Ptx.Scalar.Parallel.Grid.embed_concrete
#print axioms Ptx.Scalar.Parallel.Grid.Reference.run_concrete
#print axioms Ptx.Scalar.Parallel.GridDenseBackward.Checks.run
#print axioms Ptx.Scalar.Parallel.GridDenseBackward.Checks.large_execution_exists
#print axioms Ptx.Scalar.Parallel.GridDenseBackward.Bounds
#print axioms Ptx.Scalar.Parallel.GridDenseBackward.gateLayout
#print axioms Ptx.Scalar.Parallel.GridDenseBackward.weightLayout
#print axioms Ptx.Scalar.Parallel.GridDenseBackward.copySource
#print axioms Ptx.Scalar.Parallel.GridDenseBackward.copy_source_bound
#print axioms Ptx.Scalar.Parallel.GridDenseBackward.copyLayout
#print axioms Ptx.Scalar.Parallel.GridDenseBackward.gateInput
#print axioms Ptx.Scalar.Parallel.GridDenseBackward.weightInput
#print axioms Ptx.Scalar.Parallel.GridDenseBackward.copyInput
#print axioms Ptx.Scalar.Parallel.GridDenseBackward.packet
#print axioms Ptx.Scalar.Parallel.GridDenseBackward.Execution
#print axioms Ptx.Scalar.Parallel.GridDenseBackward.execution_exists
#print axioms Ptx.Scalar.Parallel.GridDenseBackward.Execution.g
#print axioms Ptx.Scalar.Parallel.GridDenseBackward.Execution.dw
#print axioms Ptx.Scalar.Parallel.GridDenseBackward.Execution.dx
#print axioms Ptx.Scalar.Parallel.GridDenseBackward.lengths
#print axioms Ptx.Scalar.Parallel.GridDenseBackward.input_frame
#print axioms Ptx.Scalar.Parallel.GridDenseBackward.gate_frame
#print axioms Ptx.Scalar.Parallel.GridDenseBackward.gate_result
#print axioms Ptx.Scalar.Parallel.GridDenseBackward.weight_result
#print axioms Ptx.Scalar.Parallel.GridDenseBackward.packet_word
#print axioms Ptx.Scalar.Parallel.GridDenseBackward.packet_input
#print axioms Ptx.Scalar.Parallel.GridDenseBackward.packet_weight
#print axioms Ptx.Scalar.Parallel.GridDenseBackward.packet_bias
#print axioms Ptx.Scalar.Parallel.GridDenseBackward.input_result
#print axioms Ptx.Scalar.Parallel.GridDenseBackward.gradients_stored
#print axioms Ptx.Scalar.Parallel.GridDense.completed_concrete_exists
#print axioms Ptx.Scalar.Parallel.GridDense.completed_admitted_exists
#print axioms Ptx.Scalar.Parallel.GridDense.Launch
#print axioms Ptx.Scalar.Parallel.GridDense.launch_exists
#print axioms Ptx.Scalar.Parallel.GridDense.launch_correct
#print axioms Ptx.Scalar.Parallel.GridDense.Local.initial
#print axioms Ptx.Scalar.Parallel.GridDense.Local.candidate_control
#print axioms Ptx.Scalar.Parallel.GridDense.Local.coordinates_at_entry
#print axioms Ptx.Scalar.Parallel.GridDense.Local.entry_regs
#print axioms Ptx.Scalar.Parallel.GridDense.Local.initial_reg
#print axioms Ptx.Scalar.Parallel.GridDense.Local.product_exists
#print axioms Ptx.Scalar.Parallel.GridDense.Local.reduction_exists
#print axioms Ptx.Scalar.Parallel.GridDense.Local.completed_exists
#print axioms Ptx.Scalar.Parallel.GridPointwise.extend
#print axioms Ptx.Scalar.Parallel.GridPointwise.LogicalLaunch
#print axioms Ptx.Scalar.Parallel.GridPointwise.logical_exists
#print axioms Ptx.Scalar.Parallel.GridPointwise.logical_correct
#print axioms Ptx.Scalar.Parallel.Grid.Replay.Arrays
#print axioms Ptx.Scalar.Parallel.Grid.Replay.arrays
#print axioms Ptx.Scalar.Parallel.Grid.Replay.view
#print axioms Ptx.Scalar.Parallel.Grid.Replay.install
#print axioms Ptx.Scalar.Parallel.Grid.Replay.arena
#print axioms Ptx.Scalar.Parallel.Grid.Replay.event
#print axioms Ptx.Scalar.Parallel.Grid.Replay.trace
#print axioms Ptx.Scalar.Parallel.Grid.Replay.trace_append
#print axioms Ptx.Scalar.Parallel.Grid.Replay.trace_tag
#print axioms Ptx.Scalar.Parallel.Grid.Replay.arrays_install
#print axioms Ptx.Scalar.Parallel.Grid.Replay.concrete_replays
#print axioms Ptx.Scalar.Parallel.Grid.Replay.writtenAt
#print axioms Ptx.Scalar.Parallel.Grid.Replay.latestWrite
#print axioms Ptx.Scalar.Parallel.Grid.Replay.latestWrite_none
#print axioms Ptx.Scalar.Parallel.Grid.Replay.latestWrite_origin
#print axioms Ptx.Scalar.Parallel.Grid.Replay.event_value
#print axioms Ptx.Scalar.Parallel.Grid.Replay.trace_value
#print axioms Ptx.Scalar.Parallel.Grid.Replay.load_prefix
#print axioms Ptx.Scalar.Parallel.Grid.Replay.load_source
#print axioms Ptx.Scalar.Parallel.Grid.Replay.writtenAt_some
#print axioms Ptx.Scalar.Parallel.Grid.Memory.Chronology.split_at
#print axioms Ptx.Scalar.Parallel.Grid.Memory.Chronology.cell
#print axioms Ptx.Scalar.Parallel.Grid.Memory.Chronology.initial_member
#print axioms Ptx.Scalar.Parallel.Grid.Memory.Chronology.initial_graph_member
#print axioms Ptx.Scalar.Parallel.Grid.Memory.Chronology.writtenAt_of_address
#print axioms Ptx.Scalar.Parallel.Grid.Memory.Chronology.SourceFor
#print axioms Ptx.Scalar.Parallel.Grid.Memory.Chronology.source_exists
#print axioms Ptx.Scalar.Parallel.NoSync
#print axioms Ptx.Scalar.Parallel.ConcreteSegment.frame_extra
#print axioms Ptx.Scalar.Parallel.segment_sweep
#print axioms Ptx.Scalar.Parallel.exit_sweep
#print axioms PtxTorchLean.GridDenseBackward.stored_gate
#print axioms PtxTorchLean.GridDenseBackward.input_words
#print axioms PtxTorchLean.GridDenseBackward.weight_accuracy
#print axioms PtxTorchLean.GridDenseBackward.input_accuracy
#print axioms PtxTorchLean.GridDenseBackward.bias_accuracy
#print axioms PtxTorchLean.GridDenseBackward.Correct
#print axioms PtxTorchLean.GridDenseBackward.universal_backward
#print axioms PtxTorchLean.GridDenseBackward.backward_exists
#print axioms PtxTorchLean.GridDenseForward.forward_exists

-- Compact row-local scratch program and proofs.
#print axioms Ptx.Scalar.Parallel.Dense.Compact.program_address_compatible
#print axioms Ptx.Scalar.Parallel.Dense.Compact.products_control_coordinates
#print axioms Ptx.Scalar.Parallel.Dense.Compact.round_control_coordinates
#print axioms Ptx.Scalar.Parallel.Dense.Compact.rounds_control_coordinates
#print axioms Ptx.Scalar.Parallel.Dense.Compact.control_atPC_slice
#print axioms Ptx.Scalar.Parallel.Dense.Compact.product_control_address
#print axioms Ptx.Scalar.Parallel.Dense.Compact.round_control_address
#print axioms Ptx.Scalar.Parallel.Dense.Compact.output_control_address
#print axioms Ptx.Scalar.Parallel.Dense.Compact.round_control_active
#print axioms Ptx.Scalar.Parallel.Dense.Compact.product_read_control
#print axioms Ptx.Scalar.Parallel.Dense.Compact.round_read_control
#print axioms Ptx.Scalar.Parallel.Dense.Compact.output_read_control
#print axioms Ptx.Scalar.Parallel.Dense.Compact.program_straight
#print axioms Ptx.Scalar.Parallel.Dense.Compact.fetched_store_site
#print axioms Ptx.Scalar.Parallel.Dense.Compact.fetched_load_site
#print axioms Ptx.Scalar.Parallel.Dense.Compact.fetched_exit_site
#print axioms Ptx.Scalar.Parallel.Dense.Compact.program_segment
#print axioms Ptx.Scalar.Parallel.Dense.Compact.scalar_data
#print axioms Ptx.Scalar.Parallel.Dense.Compact.fp_data
#print axioms Ptx.Scalar.Parallel.Dense.Compact.barrier_data
#print axioms Ptx.Scalar.Parallel.Dense.Compact.scalar_store_data
#print axioms Ptx.Scalar.Parallel.Dense.Compact.product_scalar_data
#print axioms Ptx.Scalar.Parallel.Dense.Compact.round_scalar_data
#print axioms Ptx.Scalar.Parallel.Dense.Compact.output_scalar_data
#print axioms Ptx.Scalar.Parallel.Dense.Compact.afterSetup
#print axioms Ptx.Scalar.Parallel.Dense.Compact.setup_execution
#print axioms Ptx.Scalar.Parallel.Dense.Compact.productFinish
#print axioms Ptx.Scalar.Parallel.Dense.Compact.product_segment
#print axioms Ptx.Scalar.Parallel.Dense.Compact.round_regular
#print axioms Ptx.Scalar.Parallel.Dense.Compact.output_regular
#print axioms Ptx.Scalar.Parallel.Dense.Compact.sharedWords
#print axioms Ptx.Scalar.Parallel.Dense.Compact.shared_words_factor
#print axioms Ptx.Scalar.Parallel.Dense.Compact.scratch_bound
#print axioms Ptx.Scalar.Parallel.Dense.Compact.leftIndex
#print axioms Ptx.Scalar.Parallel.Dense.Compact.nextIndex
#print axioms Ptx.Scalar.Parallel.Dense.Compact.rootIndex
#print axioms Ptx.Scalar.Parallel.Dense.Compact.shared_le
#print axioms Ptx.Scalar.Parallel.Dense.Compact.round_indices
#print axioms Ptx.Scalar.Parallel.Dense.Compact.output_indices
#print axioms Ptx.Scalar.Parallel.Dense.Compact.products
#print axioms Ptx.Scalar.Parallel.Dense.Compact.round
#print axioms Ptx.Scalar.Parallel.Dense.Compact.output
#print axioms Ptx.Scalar.Parallel.Dense.Compact.program
#print axioms Ptx.Scalar.Parallel.Dense.Compact.products_length
#print axioms Ptx.Scalar.Parallel.Dense.Compact.round_length
#print axioms Ptx.Scalar.Parallel.Dense.Compact.program_length
#print axioms Ptx.Scalar.Parallel.Dense.Compact.round_barrier
#print axioms Ptx.Scalar.Parallel.Dense.Compact.product_barrier
#print axioms Ptx.Scalar.Parallel.Dense.Compact.output_exit
#print axioms Ptx.Scalar.Parallel.Dense.Compact.products_fetch
#print axioms Ptx.Scalar.Parallel.Dense.Compact.program_round_split
#print axioms Ptx.Scalar.Parallel.Dense.Compact.round_fetch
#print axioms Ptx.Scalar.Parallel.Dense.Compact.output_fetch

-- Stable-softmax numerical composition and finite approximate neighborhoods.
#print axioms Ptx.Binary32.Approximate.Within
#print axioms Ptx.Binary32.Approximate.center_mem
#print axioms Ptx.Binary32.Approximate.nonempty
#print axioms Ptx.Binary32.Approximate.output_finite
#print axioms Ptx.Binary32.Approximate.monotone
#print axioms Ptx.Binary32.Approximate.total_error
#print axioms Ptx.Binary32.Approximate.rounded_center_error
#print axioms Ptx.Binary32.Approximate.WithinULP
#print axioms Ptx.Binary32.Approximate.ulp_nonnegative
#print axioms Ptx.Binary32.Approximate.ulp_nonempty
#print axioms Ptx.Binary32.Approximate.ulp_error
#print axioms Ptx.Binary32.Approximate.one_real
#print axioms Ptx.Binary32.Approximate.successor_one_real
#print axioms Ptx.Binary32.Approximate.multiple_results
#print axioms Ptx.Binary32.Approximate.signed_zeros
#print axioms Ptx.Binary32.Approximate.infinity_excluded
#print axioms Ptx.Binary32.Approximate.nan_excluded
#print axioms Ptx.Numerics.Softmax.denominatorBudget
#print axioms Ptx.Numerics.Softmax.coordinateBudget
#print axioms Ptx.Numerics.Softmax.Stages
#print axioms Ptx.Numerics.Softmax.sum_error
#print axioms Ptx.Numerics.Softmax.denominator_error
#print axioms Ptx.Numerics.Softmax.denominator_positive
#print axioms Ptx.Numerics.Softmax.exact_denominator_bounds
#print axioms Ptx.Numerics.Softmax.quotient_error
#print axioms Ptx.Numerics.Softmax.coordinate_error
#print axioms Ptx.Numerics.Softmax.normalization_error
#print axioms Ptx.Numerics.Softmax.dotBudget
#print axioms Ptx.Numerics.Softmax.BackwardStages
#print axioms Ptx.Numerics.Softmax.backward_dot_error
#print axioms Ptx.Numerics.Softmax.backwardBudget
#print axioms Ptx.Numerics.Softmax.backward_coordinate_error
#print axioms Ptx.Numerics.Softmax.exact_stages
#print axioms Ptx.Numerics.Softmax.exact_backward_stages
#print axioms Ptx.Numerics.Softmax.denominator_can_be_zero
#print axioms Ptx.Numerics.Softmax.Checks.zero_denominator_boundary
#print axioms Ptx.Numerics.Softmax.Checks.permitted_nonunit_sum
#print axioms Ptx.Numerics.Softmax.Checks.normalization_bound_attained
#print axioms Ptx.Numerics.Softmax.Checks.permitted_zero_weight
#print axioms Ptx.Numerics.Softmax.Checks.backward_uniform_row
#print axioms PtxTorchLean.Softmax.weights
#print axioms PtxTorchLean.Softmax.forward
#print axioms PtxTorchLean.Softmax.backward
#print axioms PtxTorchLean.Softmax.weights_bounds
#print axioms PtxTorchLean.Softmax.forward_formula
#print axioms PtxTorchLean.Softmax.forward_error
#print axioms PtxTorchLean.Softmax.computed_denominator_positive
#print axioms PtxTorchLean.Softmax.computed_normalization_error
#print axioms PtxTorchLean.Softmax.backward_formula
#print axioms PtxTorchLean.Softmax.backward_is_vjp
#print axioms PtxTorchLean.Softmax.backward_error
#print axioms PtxTorchLean.Softmax.backward_error_of_forward
#print axioms Ptx.Numerics.Softmax.Stages.exponential
#print axioms Ptx.Numerics.Softmax.Stages.summation
#print axioms Ptx.Numerics.Softmax.Stages.inverse
#print axioms Ptx.Numerics.Softmax.Stages.multiplication
#print axioms Ptx.Numerics.Softmax.BackwardStages.weights
#print axioms Ptx.Numerics.Softmax.BackwardStages.incoming
#print axioms Ptx.Numerics.Softmax.BackwardStages.reduction
#print axioms Ptx.Numerics.Softmax.BackwardStages.subtraction
#print axioms Ptx.Numerics.Softmax.BackwardStages.multiplication

-- Encoded rounded-real centers and nearest-even reciprocal foundations.
#print axioms Ptx.Binary32.RoundedReal.roundedDyadic
#print axioms Ptx.Binary32.RoundedReal.scaledInt_real
#print axioms Ptx.Binary32.RoundedReal.roundedDyadic_real
#print axioms Ptx.Binary32.RoundedReal.round_idempotent
#print axioms Ptx.Binary32.RoundedReal.round_range
#print axioms Ptx.Binary32.RoundedReal.word
#print axioms Ptx.Binary32.RoundedReal.decode_bits
#print axioms Ptx.Binary32.RoundedReal.word_finite
#print axioms Ptx.Binary32.RoundedReal.word_real
#print axioms Ptx.Binary32.RoundedReal.exists_word
#print axioms Ptx.Binary32.RoundedReal.word_preserves_value
#print axioms Ptx.Binary32.RoundedReal.Results
#print axioms Ptx.Binary32.RoundedReal.results_exists
#print axioms Ptx.Binary32.RoundedReal.results_error
#print axioms Ptx.Binary32.RoundedReal.unit_range
#print axioms Ptx.Binary32.RoundedReal.exp2_range
#print axioms Ptx.Binary32.RoundedReal.reciprocal_range
#print axioms Ptx.Binary32.RoundedReal.exp2_results_exists
#print axioms Ptx.Binary32.RoundedReal.reciprocal_word_exists
#print axioms Ptx.Binary32.ApproximateBounds.ulp_one
#print axioms Ptx.Binary32.ApproximateBounds.ulp_half
#print axioms Ptx.Binary32.ApproximateBounds.ulp_unit
#print axioms Ptx.Binary32.ApproximateBounds.round_unit
#print axioms Ptx.Binary32.ApproximateBounds.results_error
#print axioms Ptx.Binary32.ApproximateBounds.exp2_error
#print axioms Ptx.Binary32.RoundedRealChecks.largest_finite
#print axioms Ptx.Binary32.RoundedRealChecks.negative_endpoint
#print axioms Ptx.Binary32.RoundedRealChecks.zero_center
#print axioms Ptx.Binary32.RoundedRealChecks.smallest_subnormal_real
#print axioms Ptx.Binary32.RoundedRealChecks.smallest_subnormal_preserved
#print axioms Ptx.Binary32.RoundedRealChecks.fractional_exponent
#print axioms Ptx.Binary32.RoundedRealChecks.deep_underflow_domain
#print axioms Ptx.Binary32.RoundedRealChecks.out_of_range
#print axioms Ptx.Binary32.RoundedRealChecks.below_one_real
#print axioms Ptx.Binary32.RoundedRealChecks.center_spacing_not_encoding_distance
#print axioms Ptx.Binary32.Reciprocal.reference
#print axioms Ptx.Binary32.Reciprocal.Results
#print axioms Ptx.Binary32.Reciprocal.instDecidableResults
#print axioms Ptx.Binary32.Reciprocal.results_exists
#print axioms Ptx.Binary32.Reciprocal.input_nonzero
#print axioms Ptx.Binary32.Reciprocal.reference_finite
#print axioms Ptx.Binary32.Reciprocal.reference_real
#print axioms Ptx.Binary32.Reciprocal.results_real
#print axioms Ptx.Binary32.Reciprocal.results_error
#print axioms Ptx.Binary32.Reciprocal.half_range
#print axioms Ptx.Binary32.Reciprocal.finite_result_exists
#print axioms Ptx.Binary32.Reciprocal.result_exists_of_sum_error
#print axioms Ptx.Binary32.Reciprocal.Checks.signed_zeros
#print axioms Ptx.Binary32.Reciprocal.Checks.signed_infinities
#print axioms Ptx.Binary32.Reciprocal.Checks.signs
#print axioms Ptx.Binary32.Reciprocal.Checks.rounded_third
#print axioms Ptx.Binary32.Reciprocal.Checks.subnormal_output
#print axioms Ptx.Binary32.Reciprocal.Checks.overflow_from_subnormal
#print axioms Ptx.Binary32.Reciprocal.Checks.nan_freedom
#print axioms Ptx.Binary32.Reciprocal.Checks.finite_mismatch_rejected
#print axioms Ptx.Binary32.Reciprocal.Checks.denominator_handoff

#print axioms Ptx.Binary32.ApproximatePolicyChecks.center
#print axioms Ptx.Binary32.ApproximatePolicyChecks.output
#print axioms Ptx.Binary32.ApproximatePolicyChecks.center_real
#print axioms Ptx.Binary32.ApproximatePolicyChecks.output_real
#print axioms Ptx.Binary32.ApproximatePolicyChecks.center_ulp
#print axioms Ptx.Binary32.ApproximatePolicyChecks.output_ulp
#print axioms Ptx.Binary32.ApproximatePolicyChecks.output_spacing_not_center_spacing

#print axioms Ptx.Scalar.Reciprocal.Instr
#print axioms Ptx.Scalar.Reciprocal.Occurrence
#print axioms Ptx.Scalar.Reciprocal.occurrence
#print axioms Ptx.Scalar.Reciprocal.SupportedTarget
#print axioms Ptx.Scalar.Reciprocal.Eval
#print axioms Ptx.Scalar.Reciprocal.Step
#print axioms Ptx.Scalar.Reciprocal.eval_true_iff
#print axioms Ptx.Scalar.Reciprocal.eval_false_iff
#print axioms Ptx.Scalar.Reciprocal.eval_destination
#print axioms Ptx.Scalar.Reciprocal.eval_frame
#print axioms Ptx.Scalar.Reciprocal.eval_other
#print axioms Ptx.Scalar.Reciprocal.eval_event
#print axioms Ptx.Scalar.Reciprocal.eval_exists
#print axioms Ptx.Scalar.Reciprocal.step_origin
#print axioms Ptx.Scalar.Reciprocal.step_exists
#print axioms Ptx.Scalar.Reciprocal.step_no_fetch
#print axioms Ptx.Scalar.Reciprocal.step_unsupported_target
#print axioms Ptx.Scalar.Reciprocal.Text.mnemonic
#print axioms Ptx.Scalar.Reciprocal.Text.supportedMnemonic
#print axioms Ptx.Scalar.Reciprocal.Text.encode
#print axioms Ptx.Scalar.Reciprocal.Text.decode
#print axioms Ptx.Scalar.Reciprocal.Text.decode_encode
#print axioms Ptx.Scalar.Reciprocal.Text.decode_iff

#print axioms Ptx.Binary32.ConservativeULP.Within
#print axioms Ptx.Binary32.ConservativeULP.OutputULP
#print axioms Ptx.Binary32.ConservativeULP.center_included
#print axioms Ptx.Binary32.ConservativeULP.output_included
#print axioms Ptx.Binary32.ConservativeULP.within_iff
#print axioms Ptx.Binary32.ConservativeULP.nonempty
#print axioms Ptx.Binary32.ConservativeULP.output_finite
#print axioms Ptx.Binary32.ConservativeULP.ulp_relative
#print axioms Ptx.Binary32.ConservativeULP.ulp_coarse
#print axioms Ptx.Binary32.ConservativeULP.ulp_below_two
#print axioms Ptx.Binary32.ConservativeULP.unit_distance
#print axioms Ptx.Binary32.ConservativeULP.Results
#print axioms Ptx.Binary32.ConservativeULP.results_exists
#print axioms Ptx.Binary32.ConservativeULP.results_error
#print axioms Ptx.Binary32.ConservativeULP.exp2_results_exists
#print axioms Ptx.Binary32.ConservativeULP.exp2_error
#print axioms Ptx.Binary32.ConservativeULPChecks.boundary_included
#print axioms Ptx.Binary32.ConservativeULPChecks.negative_min_real
#print axioms Ptx.Binary32.ConservativeULPChecks.tiny_negative_allowed
#print axioms Ptx.Binary32.ConservativeULPChecks.both_zero_signs
#print axioms Ptx.Binary32.ConservativeULPChecks.infinity_excluded
#print axioms Ptx.Binary32.ConservativeULPChecks.large_count_requires_care
#print axioms Ptx.Binary32.ExpArgument.constantWord
#print axioms Ptx.Binary32.ExpArgument.constantValue
#print axioms Ptx.Binary32.ExpArgument.constant_real
#print axioms Ptx.Binary32.ExpArgument.constant_positive
#print axioms Ptx.Binary32.ExpArgument.constantError
#print axioms Ptx.Binary32.ExpArgument.budget
#print axioms Ptx.Binary32.ExpArgument.exp_nonpos_distance
#print axioms Ptx.Binary32.ExpArgument.exp2_nonpos_distance
#print axioms Ptx.Binary32.ExpArgument.base_conversion
#print axioms Ptx.Binary32.ExpArgument.product_real
#print axioms Ptx.Binary32.ExpArgument.bounded_product_range
#print axioms Ptx.Binary32.ExpArgument.argument_error
#print axioms Ptx.Binary32.ExpArgument.FiniteExp2
#print axioms Ptx.Binary32.ExpArgument.natural_exp_error
#print axioms Ptx.Binary32.ExpArgument.stages_exist
#print axioms Ptx.Binary32.ExpArgumentChecks.negative_one_product
#print axioms Ptx.Binary32.ExpArgumentChecks.zero_product
#print axioms Ptx.Binary32.ExpArgumentChecks.negative_one_stages
#print axioms Ptx.Binary32.ExpArgumentChecks.negative_one_accuracy

#print axioms Ptx.Binary32.Exponential.Supported
#print axioms Ptx.Binary32.Exponential.Results
#print axioms Ptx.Binary32.Exponential.finite_iff
#print axioms Ptx.Binary32.Exponential.zero_iff
#print axioms Ptx.Binary32.Exponential.negative_iff
#print axioms Ptx.Binary32.Exponential.positive_unsupported
#print axioms Ptx.Binary32.Exponential.nan_iff
#print axioms Ptx.Binary32.Exponential.neg_inf_iff
#print axioms Ptx.Binary32.Exponential.pos_inf_iff
#print axioms Ptx.Binary32.Exponential.results_exists_iff
#print axioms Ptx.Binary32.Exponential.results_supported
#print axioms Ptx.Binary32.Exponential.results_exists
#print axioms Ptx.Binary32.Exponential.one_allowed
#print axioms Ptx.Binary32.Exponential.finiteExp2
#print axioms Ptx.Binary32.Exponential.finite_error
#print axioms Ptx.Binary32.Exponential.Checks.positive_zero_real
#print axioms Ptx.Binary32.Exponential.Checks.negative_zero_real
#print axioms Ptx.Binary32.Exponential.Checks.signed_zeros
#print axioms Ptx.Binary32.Exponential.Checks.zero_neighbor_rejected
#print axioms Ptx.Binary32.Exponential.Checks.signed_infinities
#print axioms Ptx.Binary32.Exponential.Checks.nan_freedom
#print axioms Ptx.Binary32.Exponential.Checks.positive_finite_rejected
#print axioms Ptx.Binary32.Exponential.Checks.negative_one_real
#print axioms Ptx.Binary32.Exponential.Checks.half_real
#print axioms Ptx.Binary32.Exponential.Checks.negative_one_multiple_results
#print axioms Ptx.Binary32.Exponential.Checks.negative_subnormal_real
#print axioms Ptx.Binary32.Exponential.Checks.negative_subnormal_exists

#print axioms Ptx.Scalar.Exponential.Instr
#print axioms Ptx.Scalar.Exponential.Occurrence
#print axioms Ptx.Scalar.Exponential.occurrence
#print axioms Ptx.Scalar.Exponential.SupportedTarget
#print axioms Ptx.Scalar.Exponential.Eval
#print axioms Ptx.Scalar.Exponential.Step
#print axioms Ptx.Scalar.Exponential.eval_true_iff
#print axioms Ptx.Scalar.Exponential.eval_false_iff
#print axioms Ptx.Scalar.Exponential.eval_destination
#print axioms Ptx.Scalar.Exponential.eval_frame
#print axioms Ptx.Scalar.Exponential.eval_other
#print axioms Ptx.Scalar.Exponential.eval_event
#print axioms Ptx.Scalar.Exponential.eval_exists
#print axioms Ptx.Scalar.Exponential.eval_exists_iff
#print axioms Ptx.Scalar.Exponential.step_origin
#print axioms Ptx.Scalar.Exponential.step_exists
#print axioms Ptx.Scalar.Exponential.step_no_fetch
#print axioms Ptx.Scalar.Exponential.step_unsupported_target
#print axioms Ptx.Scalar.Exponential.Text.mnemonic
#print axioms Ptx.Scalar.Exponential.Text.supportedMnemonic
#print axioms Ptx.Scalar.Exponential.Text.encode
#print axioms Ptx.Scalar.Exponential.Text.decode
#print axioms Ptx.Scalar.Exponential.Text.decode_encode
#print axioms Ptx.Scalar.Exponential.Text.decode_iff

#print axioms Ptx.Binary32.ShiftedExp.InputBounds
#print axioms Ptx.Binary32.ShiftedExp.negative_real
#print axioms Ptx.Binary32.ShiftedExp.shift_real
#print axioms Ptx.Binary32.ShiftedExp.error
#print axioms Ptx.Binary32.ShiftedExp.equal_scores
#print axioms Ptx.Binary32.ShiftedExp.stages_exist
#print axioms Ptx.Scalar.ShiftedExp.Instr
#print axioms Ptx.Scalar.ShiftedExp.Event
#print axioms Ptx.Scalar.ShiftedExp.Eval
#print axioms Ptx.Scalar.ShiftedExp.Step
#print axioms Ptx.Scalar.ShiftedExp.Run
#print axioms Ptx.Scalar.ShiftedExp.negate
#print axioms Ptx.Scalar.ShiftedExp.shift
#print axioms Ptx.Scalar.ShiftedExp.convert
#print axioms Ptx.Scalar.ShiftedExp.exponential
#print axioms Ptx.Scalar.ShiftedExp.program
#print axioms Ptx.Scalar.ShiftedExp.text
#print axioms Ptx.Scalar.ShiftedExp.run_results
#print axioms Ptx.Scalar.ShiftedExp.correct
#print axioms Ptx.Scalar.ShiftedExp.maximal_score
#print axioms Ptx.Scalar.ShiftedExp.execution_exists
#print axioms Ptx.Scalar.ShiftedExp.Checks.spellings
#print axioms Ptx.Scalar.ShiftedExp.Checks.missing_fetch
#print axioms Ptx.Scalar.ShiftedExp.Checks.unsupported_target
#print axioms Ptx.Scalar.ShiftedExp.Checks.maximum_alias
#print axioms Ptx.Scalar.ShiftedExp.Checks.subnormal_shift
#print axioms Ptx.Scalar.ShiftedExp.Checks.endpoint_real
#print axioms Ptx.Scalar.ShiftedExp.Checks.endpoint_stages
#print axioms Ptx.Scalar.ShiftedExp.Checks.signed_zero_execution
#print axioms Ptx.Scalar.ShiftedExp.Checks.negative_shift_execution

#print axioms Ptx.Binary32.Maximum.key
#print axioms Ptx.Binary32.Maximum.choose
#print axioms Ptx.Binary32.Maximum.choose_mem
#print axioms Ptx.Binary32.Maximum.key_order
#print axioms Ptx.Binary32.Maximum.choose_real
#print axioms Ptx.Binary32.Maximum.choose_signed_zeros
#print axioms Ptx.Binary32.Maximum.choose_subnormal_boundaries
#print axioms Ptx.Binary32.Maximum.choose_self
#print axioms Ptx.Scalar.Parallel.Maximum.program_address_compatible
#print axioms Ptx.Scalar.Parallel.Maximum.controlSeed
#print axioms Ptx.Scalar.Parallel.Maximum.initial_address_control
#print axioms Ptx.Scalar.Parallel.Maximum.candidate_address_control
#print axioms Ptx.Scalar.Parallel.Maximum.publish_control_identity
#print axioms Ptx.Scalar.Parallel.Maximum.round_control_identity
#print axioms Ptx.Scalar.Parallel.Maximum.rounds_control_identity
#print axioms Ptx.Scalar.Parallel.Maximum.control_atPC_slice
#print axioms Ptx.Scalar.Parallel.Maximum.publication_control_address
#print axioms Ptx.Scalar.Parallel.Maximum.round_control_address
#print axioms Ptx.Scalar.Parallel.Maximum.output_control_address
#print axioms Ptx.Scalar.Parallel.Maximum.round_control_active
#print axioms Ptx.Scalar.Parallel.Maximum.Checks.seed
#print axioms Ptx.Scalar.Parallel.Maximum.Checks.schedule
#print axioms Ptx.Scalar.Parallel.Maximum.Checks.execute
#print axioms Ptx.Scalar.Parallel.Maximum.Checks.singleton
#print axioms Ptx.Scalar.Parallel.Maximum.Checks.negative_tree
#print axioms Ptx.Scalar.Parallel.Maximum.Checks.signed_zero_tree
#print axioms Ptx.Scalar.Parallel.Maximum.Checks.eight_tree
#print axioms Ptx.Scalar.Parallel.Maximum.Checks.negative_execution
#print axioms Ptx.Scalar.Parallel.Maximum.Checks.eight_execution
#print axioms Ptx.Scalar.Parallel.Maximum.program_straight
#print axioms Ptx.Scalar.Parallel.Maximum.scalar_site_unique
#print axioms Ptx.Scalar.Parallel.Maximum.scalar_before_arrival
#print axioms Ptx.Scalar.Parallel.Maximum.scalar_after_completion
#print axioms Ptx.Scalar.Parallel.Maximum.fetched_store_site
#print axioms Ptx.Scalar.Parallel.Maximum.trace_store_site
#print axioms Ptx.Scalar.Parallel.Maximum.fetched_exit_site
#print axioms Ptx.Scalar.Parallel.Maximum.completed_pc_bound
#print axioms Ptx.Scalar.Parallel.Maximum.completed_barrier_exists
#print axioms Ptx.Scalar.Parallel.Maximum.completed_phases
#print axioms Ptx.Scalar.Parallel.Maximum.completed_input_store
#print axioms Ptx.Scalar.Parallel.Maximum.completed_round_store
#print axioms Ptx.Scalar.Parallel.Maximum.completed_output_store
#print axioms Ptx.Scalar.Parallel.Maximum.completed_input_publication
#print axioms Ptx.Scalar.Parallel.Maximum.completed_round_publication
#print axioms Ptx.Scalar.Parallel.Maximum.Data
#print axioms Ptx.Scalar.Parallel.Maximum.ReadData
#print axioms Ptx.Scalar.Parallel.Maximum.StoreData
#print axioms Ptx.Scalar.Parallel.Maximum.initial_data
#print axioms Ptx.Scalar.Parallel.Maximum.DataInvariant
#print axioms Ptx.Scalar.Parallel.Maximum.Stores
#print axioms Ptx.Scalar.Parallel.Maximum.Reads
#print axioms Ptx.Scalar.Parallel.Maximum.dispatch_data
#print axioms Ptx.Scalar.Parallel.Maximum.step_data
#print axioms Ptx.Scalar.Parallel.Maximum.scalar_step_singleton
#print axioms Ptx.Scalar.Parallel.Maximum.program_segment
#print axioms Ptx.Scalar.Parallel.Maximum.scalar_data
#print axioms Ptx.Scalar.Parallel.Maximum.no_fp
#print axioms Ptx.Scalar.Parallel.Maximum.barrier_data
#print axioms Ptx.Scalar.Parallel.Maximum.run_data
#print axioms Ptx.Scalar.Parallel.Maximum.publish_scalar_data
#print axioms Ptx.Scalar.Parallel.Maximum.round_scalar_data
#print axioms Ptx.Scalar.Parallel.Maximum.output_scalar_data
#print axioms Ptx.Scalar.Parallel.Maximum.publishFinish
#print axioms Ptx.Scalar.Parallel.Maximum.publish_regular
#print axioms Ptx.Scalar.Parallel.Maximum.publish_effect
#print axioms Ptx.Scalar.Parallel.Maximum.Ready
#print axioms Ptx.Scalar.Parallel.Maximum.PublishInvariant
#print axioms Ptx.Scalar.Parallel.Maximum.publish_invariant_step
#print axioms Ptx.Scalar.Parallel.Maximum.publish_exists
#print axioms Ptx.Scalar.Parallel.Maximum.leftIndex
#print axioms Ptx.Scalar.Parallel.Maximum.nextIndex
#print axioms Ptx.Scalar.Parallel.Maximum.round_indices
#print axioms Ptx.Scalar.Parallel.Maximum.roundFinish
#print axioms Ptx.Scalar.Parallel.Maximum.round_prefix_regular
#print axioms Ptx.Scalar.Parallel.Maximum.round_regular
#print axioms Ptx.Scalar.Parallel.Maximum.round_effect
#print axioms Ptx.Scalar.Parallel.Maximum.RoundInvariant
#print axioms Ptx.Scalar.Parallel.Maximum.round_reads
#print axioms Ptx.Scalar.Parallel.Maximum.round_invariant_step
#print axioms Ptx.Scalar.Parallel.Maximum.round_exists
#print axioms Ptx.Scalar.Parallel.Maximum.outputFinish
#print axioms Ptx.Scalar.Parallel.Maximum.output_regular
#print axioms Ptx.Scalar.Parallel.Maximum.output_effect
#print axioms Ptx.Scalar.Parallel.Maximum.OutputInvariant
#print axioms Ptx.Scalar.Parallel.Maximum.output_invariant_step
#print axioms Ptx.Scalar.Parallel.Maximum.exit_sweep_memory
#print axioms Ptx.Scalar.Parallel.Maximum.output_exists
#print axioms Ptx.Scalar.Parallel.Maximum.selected_complete
#print axioms Ptx.Scalar.Parallel.Maximum.selected_admitted
#print axioms Ptx.Scalar.Parallel.Maximum.global_load_index
#print axioms Ptx.Scalar.Parallel.Maximum.global_prefix_unwritten
#print axioms Ptx.Scalar.Parallel.Maximum.global_read_source
#print axioms Ptx.Scalar.Parallel.Maximum.publication_read_control
#print axioms Ptx.Scalar.Parallel.Maximum.round_read_control
#print axioms Ptx.Scalar.Parallel.Maximum.output_read_control
#print axioms Ptx.Scalar.Parallel.Maximum.publicationLoad
#print axioms Ptx.Scalar.Parallel.Maximum.roundLoad
#print axioms Ptx.Scalar.Parallel.Maximum.outputLoad
#print axioms Ptx.Scalar.Parallel.Maximum.fetched_load_site
#print axioms Ptx.Scalar.Parallel.Maximum.candidate_load_address
#print axioms Ptx.Scalar.Parallel.Maximum.candidate_store_address
#print axioms Ptx.Scalar.Parallel.Maximum.sharedStorePC
#print axioms Ptx.Scalar.Parallel.Maximum.candidate_shared_owner
#print axioms Ptx.Scalar.Parallel.Maximum.candidate_global_owner
#print axioms Ptx.Scalar.Parallel.Maximum.shared_store_unique
#print axioms Ptx.Scalar.Parallel.Maximum.global_store_unique
#print axioms Ptx.Scalar.Parallel.Maximum.candidate_store_unique
#print axioms Ptx.Scalar.Parallel.Maximum.graph_writer_unique
#print axioms Ptx.Scalar.Parallel.Maximum.Bounds
#print axioms Ptx.Scalar.Parallel.Maximum.config
#print axioms Ptx.Scalar.Parallel.Maximum.initial
#print axioms Ptx.Scalar.Parallel.Maximum.publishCode
#print axioms Ptx.Scalar.Parallel.Maximum.publish
#print axioms Ptx.Scalar.Parallel.Maximum.roundPrefix
#print axioms Ptx.Scalar.Parallel.Maximum.roundSuffix
#print axioms Ptx.Scalar.Parallel.Maximum.roundCode
#print axioms Ptx.Scalar.Parallel.Maximum.round
#print axioms Ptx.Scalar.Parallel.Maximum.outputCode
#print axioms Ptx.Scalar.Parallel.Maximum.output
#print axioms Ptx.Scalar.Parallel.Maximum.program
#print axioms Ptx.Scalar.Parallel.Maximum.publishCode_length
#print axioms Ptx.Scalar.Parallel.Maximum.publish_length
#print axioms Ptx.Scalar.Parallel.Maximum.roundPrefix_length
#print axioms Ptx.Scalar.Parallel.Maximum.roundSuffix_length
#print axioms Ptx.Scalar.Parallel.Maximum.roundCode_length
#print axioms Ptx.Scalar.Parallel.Maximum.round_length
#print axioms Ptx.Scalar.Parallel.Maximum.outputCode_length
#print axioms Ptx.Scalar.Parallel.Maximum.output_length
#print axioms Ptx.Scalar.Parallel.Maximum.program_length
#print axioms Ptx.Scalar.Parallel.Maximum.bounds_depth
#print axioms Ptx.Scalar.Parallel.Maximum.width_fits
#print axioms Ptx.Scalar.Parallel.Maximum.shared_fits
#print axioms Ptx.Scalar.Parallel.Maximum.children_bound
#print axioms Ptx.Scalar.Parallel.Maximum.plane_bound
#print axioms Ptx.Scalar.Parallel.Maximum.publish_fetch
#print axioms Ptx.Scalar.Parallel.Maximum.program_round_split
#print axioms Ptx.Scalar.Parallel.Maximum.round_fetch
#print axioms Ptx.Scalar.Parallel.Maximum.output_fetch
#print axioms Ptx.Scalar.Parallel.Maximum.scratch_pointer_owner
#print axioms Ptx.Scalar.Parallel.Maximum.store_node
#print axioms Ptx.Scalar.Parallel.Maximum.shared_load_node
#print axioms Ptx.Scalar.Parallel.Maximum.read_data
#print axioms Ptx.Scalar.Parallel.Maximum.Admitted
#print axioms Ptx.Scalar.Parallel.Maximum.visible_store
#print axioms Ptx.Scalar.Parallel.Maximum.plane_publication
#print axioms Ptx.Scalar.Parallel.Maximum.child_owner
#print axioms Ptx.Scalar.Parallel.Maximum.shared_read_source
#print axioms Ptx.Scalar.MaximumSelect.code
#print axioms Ptx.Scalar.MaximumSelect.code_length
#print axioms Ptx.Scalar.MaximumSelect.finish
#print axioms Ptx.Scalar.MaximumSelect.install
#print axioms Ptx.Scalar.MaximumSelect.keyCode
#print axioms Ptx.Scalar.MaximumSelect.keyInstall
#print axioms Ptx.Scalar.MaximumSelect.key_execution
#print axioms Ptx.Scalar.MaximumSelect.selectCode
#print axioms Ptx.Scalar.MaximumSelect.selectInstall
#print axioms Ptx.Scalar.MaximumSelect.select_execution
#print axioms Ptx.Scalar.MaximumSelect.reference
#print axioms Ptx.Scalar.MaximumSelect.regular
#print axioms Ptx.Scalar.Parallel.Maximum.scalar_store_data
#print axioms Ptx.Binary32.Maximum.Tree.nodeValue
#print axioms Ptx.Binary32.Maximum.Tree.attained
#print axioms Ptx.Binary32.Maximum.Tree.subtree_upper
#print axioms Ptx.Binary32.Maximum.Tree.subtree_maximum
#print axioms Ptx.Binary32.Maximum.Tree.root_maximum
#print axioms Ptx.Binary32.Maximum.Tree.magnitude_bound
#print axioms Ptx.Binary32.Maximum.Tree.root_shifted_bounds
#print axioms Ptx.Scalar.Parallel.Maximum.completed_maximum
#print axioms Ptx.Scalar.Parallel.Maximum.completed_real_maximum
#print axioms Ptx.Scalar.Parallel.Maximum.completed_shifted_bounds

-- Bounded sum and scalar normalization public declarations.
#print axioms Ptx.Binary32.Normalize.Stages
#print axioms Ptx.Binary32.Normalize.reciprocal_bounds
#print axioms Ptx.Binary32.Normalize.product_range
#print axioms Ptx.Binary32.Normalize.correct
#print axioms Ptx.Binary32.Normalize.stages_exist
#print axioms Ptx.Scalar.Normalize.Checks.spellings
#print axioms Ptx.Scalar.Normalize.Checks.missing_fetch
#print axioms Ptx.Scalar.Normalize.Checks.unsupported_target
#print axioms Ptx.Scalar.Normalize.Checks.denominator_alias
#print axioms Ptx.Scalar.Normalize.Checks.numerator_alias_changes_computation
#print axioms Ptx.Scalar.Normalize.correct
#print axioms Ptx.Scalar.Normalize.finite_execution_exists
#print axioms Ptx.Scalar.Normalize.Instr
#print axioms Ptx.Scalar.Normalize.Event
#print axioms Ptx.Scalar.Normalize.Eval
#print axioms Ptx.Scalar.Normalize.Step
#print axioms Ptx.Scalar.Normalize.Run
#print axioms Ptx.Scalar.Normalize.reciprocal
#print axioms Ptx.Scalar.Normalize.multiply
#print axioms Ptx.Scalar.Normalize.program
#print axioms Ptx.Scalar.Normalize.text
#print axioms Ptx.Scalar.Normalize.run_results
#print axioms Ptx.Scalar.Normalize.execution_exists
#print axioms Ptx.Binary32.ShiftedExp.output_range
#print axioms Ptx.Scalar.ShiftedExp.output_range
#print axioms Ptx.Binary32.SoftmaxNormalize.numerator_bound
#print axioms Ptx.Binary32.SoftmaxNormalize.denominator_lower
#print axioms Ptx.Binary32.SoftmaxNormalize.encoded_stages
#print axioms Ptx.Binary32.SoftmaxNormalize.coordinate_accuracy
#print axioms Ptx.Scalar.Parallel.Sum.Checks.check
#print axioms Ptx.Scalar.Parallel.Sum.Checks.run
#print axioms Ptx.Scalar.Parallel.Sum.valuesAt
#print axioms Ptx.Scalar.Parallel.Sum.rounded
#print axioms Ptx.Scalar.Parallel.Sum.ideal_eq_sum
#print axioms Ptx.Scalar.Parallel.Sum.output_accuracy
#print axioms Ptx.Scalar.Parallel.Sum.completed_accuracy
#print axioms Ptx.Scalar.Parallel.Sum.completed
#print axioms Ptx.Scalar.Parallel.Sum.exists_admitted
#print axioms Ptx.Scalar.Parallel.SumNormalize.entry
#print axioms Ptx.Scalar.Parallel.SumNormalize.program
#print axioms Ptx.Scalar.Parallel.SumNormalize.run_stages
#print axioms Ptx.Scalar.Parallel.SumNormalize.execution_exists
#print axioms Ptx.Scalar.Parallel.SumNormalize.completed_coordinate_accuracy
#print axioms Ptx.Scalar.Parallel.Sum.width
#print axioms Ptx.Scalar.Parallel.Sum.shape
#print axioms Ptx.Scalar.Parallel.Sum.Bounds
#print axioms Ptx.Scalar.Parallel.Sum.global
#print axioms Ptx.Scalar.Parallel.Sum.outputIndex
#print axioms Ptx.Scalar.Parallel.Sum.sharedWords
#print axioms Ptx.Scalar.Parallel.Sum.program
#print axioms Ptx.Scalar.Parallel.Sum.threads_eq
#print axioms Ptx.Scalar.Parallel.Sum.outputBase_eq
#print axioms Ptx.Scalar.Parallel.Sum.globalWords_eq
#print axioms Ptx.Scalar.Parallel.Sum.sharedWords_eq
#print axioms Ptx.Scalar.Parallel.Sum.global_length
#print axioms Ptx.Scalar.Parallel.Sum.global_input
#print axioms Ptx.Scalar.Parallel.Sum.global_input_bang
#print axioms Ptx.Scalar.Parallel.Sum.global_weight
#print axioms Ptx.Scalar.Parallel.Sum.global_bias
#print axioms Ptx.Scalar.Parallel.Sum.denseBounds
#print axioms Ptx.Scalar.Parallel.Sum.program_length
#print axioms Ptx.Scalar.Parallel.Sum.Output
#print axioms Ptx.Scalar.Parallel.Sum.output_iff
#print axioms Ptx.Binary32.SumTree.eps_bound
#print axioms Ptx.Binary32.SumTree.rounded
#print axioms Ptx.Binary32.SumTree.ideal
#print axioms Ptx.Binary32.SumTree.budget
#print axioms Ptx.Binary32.SumTree.ideal_sum
#print axioms Ptx.Binary32.SumTree.accuracy
#print axioms Ptx.Binary32.SumTree.add_zero_accuracy
#print axioms Ptx.Binary32.SumTree.budget_bound
#print axioms Ptx.Binary32.SumTree.Checks.signed_cancellation
#print axioms Ptx.Binary32.SumTree.Checks.zero_sign_changes
#print axioms Ptx.Binary32.SumTree.Checks.subnormal_leaf
#print axioms Ptx.Binary32.SumTree.Checks.singleton_budget
#print axioms Ptx.Binary32.SumTree.Checks.largest_budget

-- Reference forward pipeline public declarations.
#print axioms Ptx.Binary32.SoftmaxForward.ExpStages
#print axioms Ptx.Binary32.SoftmaxForward.delta
#print axioms Ptx.Binary32.SoftmaxForward.exact
#print axioms Ptx.Binary32.SoftmaxForward.totalBudget
#print axioms Ptx.Binary32.SoftmaxForward.equal_scores_guard
#print axioms Ptx.Binary32.SoftmaxForward.exponentials
#print axioms Ptx.Binary32.SoftmaxForward.exact_bounds
#print axioms Ptx.Binary32.SoftmaxForward.correct
#print axioms Ptx.Scalar.SoftmaxMemory.Instr
#print axioms Ptx.Scalar.SoftmaxMemory.Eval
#print axioms Ptx.Scalar.SoftmaxMemory.Executes
#print axioms Ptx.Scalar.SoftmaxMemory.Run
#print axioms Ptx.Scalar.SoftmaxMemory.AccessAt
#print axioms Ptx.Scalar.SoftmaxMemory.eval_length
#print axioms Ptx.Scalar.SoftmaxMemory.executes_length
#print axioms Ptx.Scalar.SoftmaxMemory.access_safe
#print axioms Ptx.Scalar.SoftmaxMemory.run_memory_safe
#print axioms Ptx.Scalar.SoftmaxMemory.address
#print axioms Ptx.Scalar.SoftmaxMemory.load
#print axioms Ptx.Scalar.SoftmaxMemory.store
#print axioms Ptx.Scalar.SoftmaxMemory.write
#print axioms Ptx.Scalar.SoftmaxMemory.save
#print axioms Ptx.Scalar.SoftmaxMemory.ValidIndex
#print axioms Ptx.Scalar.SoftmaxMemory.address_index
#print axioms Ptx.Scalar.SoftmaxMemory.valid_address
#print axioms Ptx.Scalar.SoftmaxMemory.load_iff
#print axioms Ptx.Scalar.SoftmaxMemory.store_iff
#print axioms Ptx.Scalar.SoftmaxMemory.store_result
#print axioms Ptx.Scalar.SoftmaxMemory.shiftedProgram
#print axioms Ptx.Scalar.SoftmaxMemory.normalizeProgram
#print axioms Ptx.Scalar.SoftmaxMemory.ShiftedStages
#print axioms Ptx.Scalar.SoftmaxMemory.NormalizeStages
#print axioms Ptx.Scalar.SoftmaxMemory.executes_cons
#print axioms Ptx.Scalar.SoftmaxMemory.executes_nil
#print axioms Ptx.Scalar.SoftmaxMemory.binary_iff
#print axioms Ptx.Scalar.SoftmaxMemory.exponential_iff
#print axioms Ptx.Scalar.SoftmaxMemory.reciprocal_iff
#print axioms Ptx.Scalar.SoftmaxMemory.Frame
#print axioms Ptx.Scalar.SoftmaxMemory.normalize_correct
#print axioms Ptx.Scalar.SoftmaxMemory.shifted_correct
#print axioms Ptx.Scalar.SoftmaxMemory.normalize_realize
#print axioms Ptx.Scalar.SoftmaxMemory.shifted_realize
#print axioms Ptx.Scalar.SoftmaxMemory.ShiftLaunch
#print axioms Ptx.Scalar.SoftmaxMemory.NormalizeLaunch
#print axioms Ptx.Scalar.SoftmaxMemory.shifted_launch_correct
#print axioms Ptx.Scalar.SoftmaxMemory.normalize_launch_correct
#print axioms Ptx.Scalar.SoftmaxMemory.shifted_launch_memory_safe
#print axioms Ptx.Scalar.SoftmaxMemory.normalize_launch_memory_safe
#print axioms Ptx.Scalar.SoftmaxMemory.entry
#print axioms Ptx.Scalar.SoftmaxMemory.shifted_launch_realize
#print axioms Ptx.Scalar.SoftmaxMemory.normalize_launch_realize
#print axioms Ptx.Scalar.SoftmaxMemory.shifted_launch_exists
#print axioms Ptx.Scalar.SoftmaxMemory.normalize_launch_exists
#print axioms Ptx.Scalar.SoftmaxMemory.constantStore
#print axioms Ptx.Scalar.SoftmaxMemory.StoreLaunch
#print axioms Ptx.Scalar.SoftmaxMemory.constantStore_iff
#print axioms Ptx.Scalar.SoftmaxMemory.store_launch_correct
#print axioms Ptx.Scalar.SoftmaxMemory.store_launch_exists
#print axioms Ptx.Scalar.SoftmaxMemory.store_launch_memory_safe
#print axioms Ptx.Scalar.SoftmaxMemory.Checks.in_place_normalization
#print axioms Ptx.Scalar.SoftmaxMemory.Checks.restore_unit_weight
#print axioms Ptx.Scalar.SoftmaxMemory.Checks.out_of_bounds_rejected
#print axioms Ptx.Scalar.SoftmaxMemory.Checks.wrapping_index_rejected
#print axioms Ptx.Scalar.SoftmaxMemory.Checks.unsupported_target
#print axioms Ptx.Scalar.SoftmaxPipeline.target
#print axioms Ptx.Scalar.SoftmaxPipeline.exponentialStep
#print axioms Ptx.Scalar.SoftmaxPipeline.normalizationStep
#print axioms Ptx.Scalar.SoftmaxPipeline.Run
#print axioms Ptx.Scalar.SoftmaxPipeline.maximumWord
#print axioms Ptx.Scalar.SoftmaxPipeline.exponential_writes
#print axioms Ptx.Scalar.SoftmaxPipeline.normalization_writes
#print axioms Ptx.Scalar.SoftmaxPipeline.arithmetic
#print axioms Ptx.Scalar.SoftmaxPipeline.Checks.singleton_exact
#print axioms Ptx.Scalar.SoftmaxPipeline.Checks.singleton_exists
#print axioms Ptx.Scalar.SoftmaxPipeline.execution_exists
#print axioms Ptx.Scalar.Parallel.SoftmaxReductions.maximumBounds
#print axioms Ptx.Scalar.Parallel.SoftmaxReductions.maximum_frame
#print axioms Ptx.Scalar.Parallel.SoftmaxReductions.maximum_exact
#print axioms Ptx.Scalar.Parallel.SoftmaxReductions.MaximumLaunch
#print axioms Ptx.Scalar.Parallel.SoftmaxReductions.maximum_launch_correct
#print axioms Ptx.Scalar.Parallel.SoftmaxReductions.maximum_launch_exists
#print axioms Ptx.Scalar.Parallel.SoftmaxReductions.sum_launch_exists
#print axioms Ptx.Scalar.Parallel.SoftmaxReductions.sum_launch_correct
#print axioms Ptx.Scalar.Parallel.SoftmaxReductions.maximum_launch_safe
#print axioms Ptx.Scalar.Parallel.SoftmaxReductions.sum_launch_safe
#print axioms Ptx.Scalar.Parallel.SoftmaxReductions.maximum_input_bounds
#print axioms Ptx.Scalar.SoftmaxStorage.row
#print axioms Ptx.Scalar.SoftmaxStorage.bang_eq
#print axioms Ptx.Scalar.SoftmaxStorage.some_bang
#print axioms Ptx.Scalar.SoftmaxStorage.global_tail
#print axioms Ptx.Scalar.SoftmaxStorage.global_eq
#print axioms Ptx.Scalar.SoftmaxStorage.restore_weight
#print axioms Ptx.Scalar.SoftmaxStorage.pass_relations
#print axioms Ptx.Scalar.SoftmaxSweep.Run
#print axioms Ptx.Scalar.SoftmaxSweep.WritesOwn
#print axioms Ptx.Scalar.SoftmaxSweep.length
#print axioms Ptx.Scalar.SoftmaxSweep.outside
#print axioms Ptx.Scalar.SoftmaxSweep.occurrence
#print axioms Ptx.Scalar.SoftmaxSweep.exists_run
#print axioms PtxTorchLean.Softmax.rowForward
#print axioms PtxTorchLean.Softmax.rowForward_formula
#print axioms PtxTorchLean.Softmax.rowForward_error
#print axioms PtxTorchLean.SoftmaxPipeline.AccuracyGuard
#print axioms PtxTorchLean.SoftmaxPipeline.resultValue
#print axioms PtxTorchLean.SoftmaxPipeline.coordinateAllowance
#print axioms PtxTorchLean.SoftmaxPipeline.Accurate
#print axioms PtxTorchLean.SoftmaxPipeline.correct
#print axioms PtxTorchLean.SoftmaxPipeline.accurate_execution_exists
#print axioms PtxTorchLean.SoftmaxPipeline.equal_scores_guard

#print axioms Ptx.Scalar.ParallelUnary.Lane
#print axioms Ptx.Scalar.ParallelUnary.State
#print axioms Ptx.Scalar.ParallelUnary.Event
#print axioms Ptx.Scalar.ParallelUnary.Event.thread
#print axioms Ptx.Scalar.ParallelUnary.Event.pc
#print axioms Ptx.Scalar.ParallelUnary.Event.instruction
#print axioms Ptx.Scalar.ParallelUnary.Event.memory
#print axioms Ptx.Scalar.ParallelUnary.setLane
#print axioms Ptx.Scalar.ParallelUnary.input
#print axioms Ptx.Scalar.ParallelUnary.install
#print axioms Ptx.Scalar.ParallelUnary.Exec
#print axioms Ptx.Scalar.ParallelUnary.Supported
#print axioms Ptx.Scalar.ParallelUnary.Step
#print axioms Ptx.Scalar.ParallelUnary.Runs
#print axioms Ptx.Scalar.ParallelUnary.ConcreteRuns
#print axioms Ptx.Scalar.ParallelUnary.ConcreteRuns.toRuns
#print axioms Ptx.Scalar.ParallelUnary.Runs.append
#print axioms Ptx.Scalar.ParallelUnary.ConcreteRuns.append
#print axioms Ptx.Scalar.ParallelUnary.exec_other
#print axioms Ptx.Scalar.ParallelUnary.step_other
#print axioms Ptx.Scalar.ParallelUnary.exec_length
#print axioms Ptx.Scalar.ParallelUnary.step_length
#print axioms Ptx.Scalar.ParallelUnary.runs_length
#print axioms Ptx.Scalar.ParallelUnary.exec_memory_safe
#print axioms Ptx.Scalar.ParallelUnary.step_memory_safe
#print axioms Ptx.Scalar.ParallelUnary.runs_memory_safe
#print axioms Ptx.Scalar.ParallelUnary.scalar_next_origin
#print axioms Ptx.Scalar.ParallelUnary.scalar_halted_origin
#print axioms Ptx.Scalar.ParallelUnary.exec_origin
#print axioms Ptx.Scalar.ParallelUnary.step_origin
#print axioms Ptx.Scalar.ParallelUnary.runs_fetch
#print axioms Ptx.Scalar.ParallelUnary.step_memory_origin
#print axioms Ptx.Scalar.ParallelUnary.step_frame
#print axioms Ptx.Scalar.ParallelUnary.runs_frame
#print axioms Ptx.Scalar.ParallelUnary.exec_exponential_supported
#print axioms Ptx.Scalar.ParallelUnary.Memory.Chronology.InitialReads
#print axioms Ptx.Scalar.ParallelUnary.Memory.Chronology.FutureStores
#print axioms Ptx.Scalar.ParallelUnary.Memory.Chronology.initial_graph_member
#print axioms Ptx.Scalar.ParallelUnary.Memory.Chronology.SourceFor
#print axioms Ptx.Scalar.ParallelUnary.Memory.Chronology.source_exists
#print axioms Ptx.Scalar.ParallelUnary.Memory.Chronology.chosenSource
#print axioms Ptx.Scalar.ParallelUnary.Memory.Chronology.chronologicalCoherence
#print axioms Ptx.Scalar.ParallelUnary.Memory.Chronology.chosenSource_spec
#print axioms Ptx.Scalar.ParallelUnary.Memory.Chronology.initial_certificate
#print axioms Ptx.Scalar.ParallelUnary.Memory.Chronology.admitted_of_initial_reads
#print axioms Ptx.Scalar.ParallelUnary.Memory.Chronology.rank
#print axioms Ptx.Scalar.ParallelUnary.Memory.Chronology.program_origin
#print axioms Ptx.Scalar.ParallelUnary.Memory.Chronology.initial_origin
#print axioms Ptx.Scalar.ParallelUnary.Memory.Chronology.initial_bound
#print axioms Ptx.Scalar.ParallelUnary.Memory.Chronology.initial_rank
#print axioms Ptx.Scalar.ParallelUnary.Memory.Chronology.program_same_position
#print axioms Ptx.Scalar.ParallelUnary.Memory.Chronology.rank_injective
#print axioms Ptx.Scalar.ParallelUnary.Memory.Chronology.program_before
#print axioms Ptx.Scalar.ParallelUnary.Memory.Chronology.initial_iff
#print axioms Ptx.Scalar.ParallelUnary.Memory.Chronology.no_release
#print axioms Ptx.Scalar.ParallelUnary.Memory.Chronology.initial_position
#print axioms Ptx.Scalar.ParallelUnary.Memory.Chronology.initial_before
#print axioms Ptx.Scalar.ParallelUnary.Memory.Chronology.base_before
#print axioms Ptx.Scalar.ParallelUnary.StraightInstr
#print axioms Ptx.Scalar.ParallelUnary.Straight
#print axioms Ptx.Scalar.ParallelUnary.cursor
#print axioms Ptx.Scalar.ParallelUnary.scalar_next_pc
#print axioms Ptx.Scalar.ParallelUnary.exec_progress
#print axioms Ptx.Scalar.ParallelUnary.step_progress
#print axioms Ptx.Scalar.ParallelUnary.TraceProgress
#print axioms Ptx.Scalar.ParallelUnary.runs_progress
#print axioms Ptx.Scalar.ParallelUnary.position_iff_pc
#print axioms Ptx.Scalar.ParallelUnary.same_site_unique
#print axioms Ptx.Scalar.ParallelUnary.step_cursor_le
#print axioms Ptx.Scalar.ParallelUnary.runs_site
#print axioms Ptx.Scalar.ParallelUnary.Memory.access
#print axioms Ptx.Scalar.ParallelUnary.Memory.access_origin
#print axioms Ptx.Scalar.ParallelUnary.Memory.labels
#print axioms Ptx.Scalar.ParallelUnary.Memory.graph
#print axioms Ptx.Scalar.ParallelUnary.Memory.Admitted
#print axioms Ptx.Scalar.ParallelUnary.Memory.labels_unique
#print axioms Ptx.Scalar.ParallelUnary.Memory.labels_origin
#print axioms Ptx.Scalar.ParallelUnary.Memory.source_initial_of_future
#print axioms Ptx.Scalar.ParallelUnary.Memory.step_access_complete
#print axioms Ptx.Scalar.ParallelUnary.Memory.run_access_complete
#print axioms Ptx.Scalar.ParallelUnary.Memory.run_graph_complete
#print axioms Ptx.Scalar.ParallelUnary.Memory.program_write_origin
#print axioms Ptx.Scalar.ParallelUnary.Memory.initial_origin
#print axioms Ptx.Scalar.ParallelUnary.Memory.initial_read_value
#print axioms Ptx.Scalar.SoftmaxParallel.Run
#print axioms Ptx.Scalar.SoftmaxParallel.refines
#print axioms Ptx.Scalar.SoftmaxParallel.of_reference
#print axioms Ptx.Scalar.SoftmaxParallel.output_equivalence
#print axioms Ptx.Scalar.SoftmaxParallel.execution_exists
#print axioms Ptx.Scalar.SoftmaxParallel.Checks.singleton_exact
#print axioms Ptx.Scalar.SoftmaxParallel.Checks.singleton_exists
#print axioms Ptx.Scalar.UnaryPointwise.Checks.wrong_load_executes
#print axioms Ptx.Scalar.UnaryPointwise.Checks.wrong_load_rejected
#print axioms Ptx.Scalar.UnaryPointwise.Checks.interleaved_loads
#print axioms Ptx.Scalar.UnaryPointwise.Op
#print axioms Ptx.Scalar.UnaryPointwise.target
#print axioms Ptx.Scalar.UnaryPointwise.Result
#print axioms Ptx.Scalar.UnaryPointwise.Bounds
#print axioms Ptx.Scalar.UnaryPointwise.Spec
#print axioms Ptx.Scalar.UnaryPointwise.sequentialStep
#print axioms Ptx.Scalar.UnaryPointwise.sequential_writes
#print axioms Ptx.Scalar.UnaryPointwise.sequential_spec
#print axioms Ptx.Scalar.UnaryPointwise.pointer
#print axioms Ptx.Scalar.UnaryPointwise.initial
#print axioms Ptx.Scalar.UnaryPointwise.Addresses
#print axioms Ptx.Scalar.UnaryPointwise.initial_addresses
#print axioms Ptx.Scalar.UnaryPointwise.step_addresses
#print axioms Ptx.Scalar.UnaryPointwise.runs_addresses
#print axioms Ptx.Scalar.UnaryPointwise.step_memory
#print axioms Ptx.Scalar.UnaryPointwise.runs_memory
#print axioms Ptx.Scalar.UnaryPointwise.run_memory
#print axioms Ptx.Scalar.UnaryPointwise.HaltSite
#print axioms Ptx.Scalar.UnaryPointwise.step_halt_site
#print axioms Ptx.Scalar.UnaryPointwise.runs_halt_site
#print axioms Ptx.Scalar.UnaryPointwise.completed_pc
#print axioms Ptx.Scalar.UnaryPointwise.completed_store
#print axioms Ptx.Scalar.UnaryPointwise.Scratch
#print axioms Ptx.Scalar.UnaryPointwise.Data
#print axioms Ptx.Scalar.UnaryPointwise.initial_data
#print axioms Ptx.Scalar.UnaryPointwise.ReadValues
#print axioms Ptx.Scalar.UnaryPointwise.step_data
#print axioms Ptx.Scalar.UnaryPointwise.runs_data
#print axioms Ptx.Scalar.UnaryPointwise.admitted_reads
#print axioms Ptx.Scalar.UnaryPointwise.run_data
#print axioms Ptx.Scalar.UnaryPointwise.store_results
#print axioms Ptx.Scalar.UnaryPointwise.input_install
#print axioms Ptx.Scalar.UnaryPointwise.install_install
#print axioms Ptx.Scalar.UnaryPointwise.LaneResult
#print axioms Ptx.Scalar.UnaryPointwise.normalize_lane
#print axioms Ptx.Scalar.UnaryPointwise.shifted_lane
#print axioms Ptx.Scalar.UnaryPointwise.lane_realize
#print axioms Ptx.Scalar.UnaryPointwise.InitialReads
#print axioms Ptx.Scalar.UnaryPointwise.realize_with_seeds
#print axioms Ptx.Scalar.UnaryPointwise.realize
#print axioms Ptx.Scalar.UnaryPointwise.initial_reads_bounded
#print axioms Ptx.Scalar.UnaryPointwise.Launch
#print axioms Ptx.Scalar.UnaryPointwise.launch_bounds
#print axioms Ptx.Scalar.UnaryPointwise.launch_spec
#print axioms Ptx.Scalar.UnaryPointwise.launch_safe
#print axioms Ptx.Scalar.UnaryPointwise.launch_realize
#print axioms Ptx.Scalar.UnaryPointwise.ownLoad
#print axioms Ptx.Scalar.UnaryPointwise.commonLoad
#print axioms Ptx.Scalar.UnaryPointwise.ownStore
#print axioms Ptx.Scalar.UnaryPointwise.exitInstr
#print axioms Ptx.Scalar.UnaryPointwise.arithmetic
#print axioms Ptx.Scalar.UnaryPointwise.body
#print axioms Ptx.Scalar.UnaryPointwise.program
#print axioms Ptx.Scalar.UnaryPointwise.storePC
#print axioms Ptx.Scalar.UnaryPointwise.exitPC
#print axioms Ptx.Scalar.UnaryPointwise.body_length
#print axioms Ptx.Scalar.UnaryPointwise.program_length
#print axioms Ptx.Scalar.UnaryPointwise.fetch_own
#print axioms Ptx.Scalar.UnaryPointwise.fetch_common
#print axioms Ptx.Scalar.UnaryPointwise.fetch_store
#print axioms Ptx.Scalar.UnaryPointwise.fetch_exit
#print axioms Ptx.Scalar.UnaryPointwise.ScalarAllowed
#print axioms Ptx.Scalar.UnaryPointwise.scalar_sites
#print axioms Ptx.Scalar.UnaryPointwise.scalar_allowed
#print axioms Ptx.Scalar.UnaryPointwise.straight
#print axioms Ptx.Scalar.UnaryPointwise.pointer_index
#print axioms Ptx.Scalar.UnaryPointwise.stores_follow_read
#print axioms Ptx.Scalar.UnaryPointwise.read_initial
#print axioms Ptx.Scalar.UnaryPointwise.reads_initial
#print axioms Ptx.Scalar.ParallelUnary.step_stored
#print axioms Ptx.Scalar.ParallelUnary.runs_stored
#print axioms Ptx.Scalar.UnaryPointwise.events_nodup
#print axioms Ptx.Scalar.UnaryPointwise.stores_unique
#print axioms Ptx.Scalar.UnaryPointwise.stored_final
#print axioms Ptx.Scalar.UnaryPointwise.sequential_realize
#print axioms PtxTorchLean.SoftmaxParallel.correct
#print axioms PtxTorchLean.SoftmaxParallel.accurate_execution_exists

-- Parallel softmax backward: all public declarations.
#print axioms Ptx.Binary32.BackwardDot.power_fixed
#print axioms Ptx.Binary32.BackwardDot.round_power_bound
#print axioms Ptx.Binary32.BackwardDot.rounded
#print axioms Ptx.Binary32.BackwardDot.ideal
#print axioms Ptx.Binary32.BackwardDot.budget
#print axioms Ptx.Binary32.BackwardDot.ideal_sum
#print axioms Ptx.Binary32.BackwardDot.finite_fixed
#print axioms Ptx.Binary32.BackwardDot.accuracy
#print axioms Ptx.Binary32.BackwardDot.add_zero_accuracy
#print axioms Ptx.Binary32.BackwardDot.Checks.cancellation
#print axioms Ptx.Binary32.BackwardDot.Checks.coordinate
#print axioms Ptx.Binary32.BackwardDot.Checks.signed_zero
#print axioms Ptx.Binary32.BackwardDot.Checks.subnormal
#print axioms Ptx.Binary32.BackwardDot.valuesAt
#print axioms Ptx.Binary32.BackwardDot.vector_rounded
#print axioms Ptx.Binary32.BackwardDot.vector_budget
#print axioms Ptx.Binary32.BackwardDot.ideal_eq_sum
#print axioms Ptx.Binary32.BackwardDot.output_accuracy
#print axioms Ptx.Scalar.Parallel.Pointwise.DifferenceChecks.run
#print axioms Ptx.Scalar.Parallel.SoftmaxBackward.Run
#print axioms Ptx.Scalar.Parallel.SoftmaxBackward.correct
#print axioms Ptx.Scalar.Parallel.SoftmaxBackward.execution_exists
#print axioms Ptx.Scalar.Parallel.SoftmaxBackward.TraceSafe
#print axioms Ptx.Scalar.Parallel.SoftmaxBackward.PointwiseSafe
#print axioms Ptx.Scalar.Parallel.SoftmaxBackward.access_safe
#print axioms Ptx.Scalar.Parallel.SoftmaxBackward.Checks.singleton_exact
#print axioms Ptx.Scalar.Parallel.SoftmaxBackward.Checks.singleton_exists
#print axioms Ptx.Scalar.Parallel.SoftmaxBackwardDot.global
#print axioms Ptx.Scalar.Parallel.SoftmaxBackwardDot.global_length
#print axioms Ptx.Scalar.Parallel.SoftmaxBackwardDot.global_probability
#print axioms Ptx.Scalar.Parallel.SoftmaxBackwardDot.global_sensitivity
#print axioms Ptx.Scalar.Parallel.SoftmaxBackwardDot.global_probability_bang
#print axioms Ptx.Scalar.Parallel.SoftmaxBackwardDot.global_sensitivity_bang
#print axioms Ptx.Scalar.Parallel.SoftmaxBackwardDot.global_bias
#print axioms Ptx.Scalar.Parallel.SoftmaxBackwardDot.Output
#print axioms Ptx.Scalar.Parallel.SoftmaxBackwardDot.output_iff
#print axioms Ptx.Scalar.Parallel.SoftmaxBackwardDot.launch_correct
#print axioms Ptx.Scalar.Parallel.SoftmaxBackwardDot.launch_prefix
#print axioms Ptx.Scalar.Parallel.SoftmaxBackwardDot.launch_exists
#print axioms Ptx.Scalar.Parallel.SoftmaxBackwardDot.launch_safe
#print axioms Ptx.Scalar.Parallel.SoftmaxBackwardDot.Checks.run
#print axioms Ptx.Scalar.Parallel.SoftmaxBackwardDot.output_accuracy
#print axioms Ptx.Scalar.Parallel.SoftmaxBackwardDot.launch_accuracy
#print axioms Ptx.Scalar.Parallel.SoftmaxBackward.ExecutionChecks.run
#print axioms Ptx.Scalar.Parallel.SoftmaxBackward.FullRun
#print axioms Ptx.Scalar.Parallel.SoftmaxBackward.entry_is_storage_view
#print axioms Ptx.Scalar.Parallel.SoftmaxBackward.full_execution_exists
#print axioms Ptx.Scalar.Parallel.SoftmaxBackward.differenceBase
#print axioms Ptx.Scalar.Parallel.SoftmaxBackward.gradientBase
#print axioms Ptx.Scalar.Parallel.SoftmaxBackward.width_bound
#print axioms Ptx.Scalar.Parallel.SoftmaxBackward.differenceLayout
#print axioms Ptx.Scalar.Parallel.SoftmaxBackward.gradientLayout
#print axioms Ptx.Scalar.Parallel.SoftmaxBackward.extend
#print axioms Ptx.Scalar.Parallel.SoftmaxBackward.extend_length
#print axioms Ptx.Scalar.Parallel.SoftmaxBackward.extend_prefix
#print axioms Ptx.Scalar.Parallel.SoftmaxBackward.bang_eq
#print axioms Ptx.Scalar.Parallel.SoftmaxBackward.saved_word
#print axioms Ptx.Scalar.Parallel.SoftmaxBackward.row_is_prefix
#print axioms Ptx.Binary32.SoftmaxBackwardNumeric.Result
#print axioms Ptx.Binary32.SoftmaxBackwardNumeric.difference
#print axioms Ptx.Binary32.SoftmaxBackwardNumeric.gradient
#print axioms Ptx.Binary32.SoftmaxBackwardNumeric.subError
#print axioms Ptx.Binary32.SoftmaxBackwardNumeric.mulError
#print axioms Ptx.Binary32.SoftmaxBackwardNumeric.result_exists
#print axioms Ptx.Binary32.SoftmaxBackwardNumeric.stages
#print axioms Ptx.Binary32.SoftmaxBackwardNumeric.accuracy
#print axioms PtxTorchLean.SoftmaxBackward.gradientValue
#print axioms PtxTorchLean.SoftmaxBackward.allowance
#print axioms PtxTorchLean.SoftmaxBackward.kernel_accuracy
#print axioms PtxTorchLean.SoftmaxBackward.Accurate
#print axioms PtxTorchLean.SoftmaxBackward.correct
#print axioms PtxTorchLean.SoftmaxBackward.accurate_execution_exists
#print axioms PtxTorchLean.Softmax.rowBackward
#print axioms PtxTorchLean.Softmax.rowBackward_formula
#print axioms PtxTorchLean.Softmax.rowBackward_is_vjp
#print axioms PtxTorchLean.SoftmaxBackward.forward_report

-- Restricted hardware export (not a verified compiler).
#print axioms Ptx.Hardware.Dense.guard
#print axioms Ptx.Hardware.Dense.word
#print axioms Ptx.Hardware.Dense.address
#print axioms Ptx.Hardware.Dense.floatWord
#print axioms Ptx.Hardware.Dense.scalar
#print axioms Ptx.Hardware.Dense.instruction
#print axioms Ptx.Hardware.Dense.exportCase
#print axioms Ptx.Hardware.Dense.Checks.reject_unsupported_local
#print axioms Ptx.Hardware.Dense.Checks.reject_memory_as_local
#print axioms Ptx.Hardware.Dense.Checks.reject_arithmetic_as_memory
#print axioms Ptx.Hardware.Dense.Checks.reject_other_barrier
#print axioms Ptx.Hardware.Dense.Checks.run
#print axioms main

-- Numerical Poisson reference, generic tensor algebra and bounded solver.
#print axioms PtxTorchLean.Poisson.Mat
#print axioms PtxTorchLean.Poisson.matrix
#print axioms PtxTorchLean.Poisson.transpose
#print axioms PtxTorchLean.Poisson.hadamard
#print axioms PtxTorchLean.Poisson.plus
#print axioms PtxTorchLean.Poisson.localAction
#print axioms PtxTorchLean.Poisson.localLoad
#print axioms PtxTorchLean.Poisson.zeroBoundary
#print axioms PtxTorchLean.Poisson.zeroBoundary_boundary
#print axioms PtxTorchLean.Poisson.zeroBoundary_interior
#print axioms PtxTorchLean.Poisson.sineSolution
#print axioms PtxTorchLean.Poisson.sineSource
#print axioms PtxTorchLean.Poisson.sineGradient
#print axioms PtxTorchLean.Poisson.lobattoNodes
#print axioms PtxTorchLean.Poisson.gaussRule
#print axioms PtxTorchLean.Poisson.lagrangeBasis
#print axioms PtxTorchLean.Poisson.Mesh
#print axioms PtxTorchLean.Poisson.quadrilateralSquare
#print axioms PtxTorchLean.Poisson.Operator
#print axioms PtxTorchLean.Poisson.makeOperator
#print axioms PtxTorchLean.Poisson.apply
#print axioms PtxTorchLean.Poisson.applyInterior
#print axioms PtxTorchLean.Poisson.load
#print axioms PtxTorchLean.Poisson.Options
#print axioms PtxTorchLean.Poisson.Reason
#print axioms PtxTorchLean.Poisson.Result
#print axioms PtxTorchLean.Poisson.solvePCG
#print axioms PtxTorchLean.Poisson.errorNorms
#print axioms PtxTorchLean.Poisson.CLI.jsonFloat
#print axioms PtxTorchLean.Poisson.CLI.evaluate
#print axioms PtxTorchLean.Poisson.CLI.run
#print axioms PtxTorchLean.Poisson.Checks.run

-- Poisson computation and exact residual certification (no PTX trace refinement).
#print axioms PtxTorchLean.Poisson.Binary64.unpacked_mul_comm
#print axioms PtxTorchLean.Poisson.Binary64.mul_comm
#print axioms PtxTorchLean.Poisson.Binary64.round
#print axioms PtxTorchLean.Poisson.Binary64.reduce256
#print axioms PtxTorchLean.Poisson.Binary64.cancellation
#print axioms PtxTorchLean.Poisson.Binary64.reduction_order_counterexample
#print axioms PtxTorchLean.Poisson.Correspondence.Registers
#print axioms PtxTorchLean.Poisson.Correspondence.Op
#print axioms PtxTorchLean.Poisson.Correspondence.step
#print axioms PtxTorchLean.Poisson.Correspondence.run
#print axioms PtxTorchLean.Poisson.Correspondence.contractionCode
#print axioms PtxTorchLean.Poisson.Correspondence.contraction_correct
#print axioms PtxTorchLean.Poisson.Correspondence.Grid
#print axioms PtxTorchLean.Poisson.Correspondence.contraction
#print axioms PtxTorchLean.Poisson.Correspondence.contraction_eq_fold
#print axioms PtxTorchLean.Poisson.Correspondence.product
#print axioms PtxTorchLean.Poisson.Correspondence.transposed
#print axioms PtxTorchLean.Poisson.Correspondence.weighted
#print axioms PtxTorchLean.Poisson.Correspondence.summed
#print axioms PtxTorchLean.Poisson.Correspondence.entries
#print axioms PtxTorchLean.Poisson.Correspondence.entries_matrix
#print axioms PtxTorchLean.Poisson.Correspondence.entries_product
#print axioms PtxTorchLean.Poisson.Correspondence.entries_transpose
#print axioms PtxTorchLean.Poisson.Correspondence.entries_weighted
#print axioms PtxTorchLean.Poisson.Correspondence.entries_summed
#print axioms PtxTorchLean.Poisson.Correspondence.Planes
#print axioms PtxTorchLean.Poisson.Correspondence.phase1
#print axioms PtxTorchLean.Poisson.Correspondence.phase2
#print axioms PtxTorchLean.Poisson.Correspondence.phase3
#print axioms PtxTorchLean.Poisson.Correspondence.phase4
#print axioms PtxTorchLean.Poisson.Correspondence.phase5
#print axioms PtxTorchLean.Poisson.Correspondence.cell
#print axioms PtxTorchLean.Poisson.Correspondence.cell_correspondence
#print axioms PtxTorchLean.Poisson.Correspondence.cell_float_correspondence
#print axioms PtxTorchLean.Poisson.Correspondence.scatterStep
#print axioms PtxTorchLean.Poisson.Correspondence.scatter_gather
#print axioms PtxTorchLean.Poisson.Correspondence.assemble
#print axioms PtxTorchLean.Poisson.Correspondence.assembly_correspondence
#print axioms PtxTorchLean.Poisson.Correspondence.distinct_writers_commute
#print axioms PtxTorchLean.Poisson.Correspondence.Connectivity
#print axioms PtxTorchLean.Poisson.Correspondence.gathered
#print axioms PtxTorchLean.Poisson.Correspondence.contributions
#print axioms PtxTorchLean.Poisson.Correspondence.operator
#print axioms PtxTorchLean.Poisson.Correspondence.tensorContributions
#print axioms PtxTorchLean.Poisson.Correspondence.tensorOperator
#print axioms PtxTorchLean.Poisson.Correspondence.operator_correspondence
#print axioms PtxTorchLean.Poisson.Correspondence.operator_float_correspondence
#print axioms PtxTorchLean.Poisson.Correspondence.interior_float_correspondence
#print axioms PtxTorchLean.Poisson.Correspondence.row_major_bound
#print axioms PtxTorchLean.Poisson.Correspondence.row_major_injective
#print axioms PtxTorchLean.Poisson.Correspondence.shared_offset_bound
#print axioms PtxTorchLean.Poisson.Certificate.Problem
#print axioms PtxTorchLean.Poisson.Certificate.exactApply
#print axioms PtxTorchLean.Poisson.Certificate.residual
#print axioms PtxTorchLean.Poisson.Certificate.squareSum
#print axioms PtxTorchLean.Poisson.Certificate.rhsSquare
#print axioms PtxTorchLean.Poisson.Certificate.thresholdSquare
#print axioms PtxTorchLean.Poisson.Certificate.Accepts
#print axioms PtxTorchLean.Poisson.Certificate.scatterVectorStep
#print axioms PtxTorchLean.Poisson.Certificate.scatterVectorStep_get
#print axioms PtxTorchLean.Poisson.Certificate.scatterVector_fold
#print axioms PtxTorchLean.Poisson.Certificate.computedApply
#print axioms PtxTorchLean.Poisson.Certificate.computedApply_get
#print axioms PtxTorchLean.Poisson.Certificate.computedResidual
#print axioms PtxTorchLean.Poisson.Certificate.computedResidual_get
#print axioms PtxTorchLean.Poisson.Certificate.computedSquare
#print axioms PtxTorchLean.Poisson.Certificate.computedSquare_eq
#print axioms PtxTorchLean.Poisson.Certificate.check
#print axioms PtxTorchLean.Poisson.Certificate.realNorm
#print axioms PtxTorchLean.Poisson.Certificate.check_sound
#print axioms PtxTorchLean.Poisson.Certificate.squareSum_eq_sum
#print axioms PtxTorchLean.Poisson.Certificate.squareSum_nonneg
#print axioms PtxTorchLean.Poisson.Certificate.realNorm_eq
#print axioms PtxTorchLean.Poisson.Certificate.certified_residual
#print axioms PtxTorchLean.Poisson.Certificate.Input.decodeWord
#print axioms PtxTorchLean.Poisson.Certificate.Input.decodeWord_real
#print axioms PtxTorchLean.Poisson.Certificate.Input.decode
#print axioms PtxTorchLean.Poisson.Certificate.Input.sized
#print axioms PtxTorchLean.Poisson.Certificate.Input.index
#print axioms PtxTorchLean.Poisson.Certificate.Input.Request
#print axioms PtxTorchLean.Poisson.Certificate.Input.parse
#print axioms PtxTorchLean.Poisson.Certificate.Input.acceptedRequest
#print axioms PtxTorchLean.Poisson.Certificate.Input.acceptedRequest_sound
#print axioms PtxTorchLean.Poisson.Certificate.Input.evaluate
#print axioms PtxTorchLean.Poisson.Certificate.Checks.recordedGpuInput
#print axioms PtxTorchLean.Poisson.Certificate.Checks.recorded_gpu_accepted
#print axioms PtxTorchLean.Poisson.Certificate.Checks.wrongInteriorInput
#print axioms PtxTorchLean.Poisson.Certificate.Checks.wrong_interior_rejected
#print axioms PtxTorchLean.Poisson.Certificate.Checks.finite_word_exact
#print axioms PtxTorchLean.Poisson.Certificate.Checks.infinity_rejected
#print axioms PtxTorchLean.Poisson.Certificate.Checks.nan_rejected

#print axioms PtxTorchLean.Poisson.PTX.sub_software
#print axioms PtxTorchLean.Poisson.PTX.Byte
#print axioms PtxTorchLean.Poisson.PTX.Word
#print axioms PtxTorchLean.Poisson.PTX.Memory
#print axioms PtxTorchLean.Poisson.PTX.byte
#print axioms PtxTorchLean.Poisson.PTX.read64
#print axioms PtxTorchLean.Poisson.PTX.write64
#print axioms PtxTorchLean.Poisson.PTX.write64_at
#print axioms PtxTorchLean.Poisson.PTX.write64_outside
#print axioms PtxTorchLean.Poisson.PTX.read64_write64
#print axioms PtxTorchLean.Poisson.PTX.read64_write64_disjoint
#print axioms PtxTorchLean.Poisson.PTX.Valid64
#print axioms PtxTorchLean.Poisson.PTX.valid_nonwrapping
#print axioms PtxTorchLean.Poisson.PTX.address64
#print axioms PtxTorchLean.Poisson.PTX.address64_exact
#print axioms PtxTorchLean.Poisson.PTX.Kernel.Checks.initial
#print axioms PtxTorchLean.Poisson.PTX.Kernel.Checks.context
#print axioms PtxTorchLean.Poisson.PTX.Kernel.Checks.code
#print axioms PtxTorchLean.Poisson.PTX.Kernel.Checks.subtract_stored_words
#print axioms PtxTorchLean.Poisson.PTX.Kernel.Checks.no_return_no_success
#print axioms PtxTorchLean.Poisson.PTX.Kernel.Checks.misaligned_load_rejected
#print axioms PtxTorchLean.Poisson.PTX.Kernel.Checks.short_allocation_rejected
#print axioms PtxTorchLean.Poisson.PTX.Kernel.Checks.below_allocation_rejected
#print axioms PtxTorchLean.Poisson.PTX.Kernel.Checks.padded_lane_needs_no_memory
#print axioms PtxTorchLean.Poisson.PTX.Kernel.Context
#print axioms PtxTorchLean.Poisson.PTX.Kernel.Instr
#print axioms PtxTorchLean.Poisson.PTX.Kernel.State
#print axioms PtxTorchLean.Poisson.PTX.Kernel.u32
#print axioms PtxTorchLean.Poisson.PTX.Kernel.scalar
#print axioms PtxTorchLean.Poisson.PTX.Kernel.advance
#print axioms PtxTorchLean.Poisson.PTX.Kernel.halt
#print axioms PtxTorchLean.Poisson.PTX.Kernel.simple
#print axioms PtxTorchLean.Poisson.PTX.Kernel.Eval
#print axioms PtxTorchLean.Poisson.PTX.Kernel.Exec
#print axioms PtxTorchLean.Poisson.PTX.Kernel.Step
#print axioms PtxTorchLean.Poisson.PTX.Kernel.Run
#print axioms PtxTorchLean.Poisson.PTX.Kernel.simple_pc
#print axioms PtxTorchLean.Poisson.PTX.Kernel.eval_pc
#print axioms PtxTorchLean.Poisson.PTX.Kernel.exec_fetched
#print axioms PtxTorchLean.Poisson.PTX.Kernel.run_exec
#print axioms PtxTorchLean.Poisson.PTX.Kernel.exec_ordinary_iff
#print axioms PtxTorchLean.Poisson.PTX.Kernel.exec_nonhalting_iff
#print axioms PtxTorchLean.Poisson.PTX.Kernel.exec_halting_iff
#print axioms PtxTorchLean.Poisson.PTX.Kernel.block_exec
#print axioms PtxTorchLean.Poisson.PTX.Kernel.exec_block
#print axioms PtxTorchLean.Poisson.PTX.Kernel.step
#print axioms PtxTorchLean.Poisson.PTX.Kernel.execute
#print axioms PtxTorchLean.Poisson.PTX.Kernel.step_sound
#print axioms PtxTorchLean.Poisson.PTX.Kernel.execute_sound
#print axioms PtxTorchLean.Poisson.PTX.Kernel.Residual.setup_address
#print axioms PtxTorchLean.Poisson.PTX.Kernel.Residual.field_valid
#print axioms PtxTorchLean.Poisson.PTX.Kernel.Residual.array_coordinate
#print axioms PtxTorchLean.Poisson.PTX.Registers
#print axioms PtxTorchLean.Poisson.PTX.decode
#print axioms PtxTorchLean.Poisson.PTX.encode
#print axioms PtxTorchLean.Poisson.PTX.decode_encode
#print axioms PtxTorchLean.Poisson.PTX.FP
#print axioms PtxTorchLean.Poisson.PTX.FP.apply
#print axioms PtxTorchLean.Poisson.PTX.FP.Result
#print axioms PtxTorchLean.Poisson.PTX.FP.result_exists
#print axioms PtxTorchLean.Poisson.PTX.Space
#print axioms PtxTorchLean.Poisson.PTX.State
#print axioms PtxTorchLean.Poisson.PTX.Operand
#print axioms PtxTorchLean.Poisson.PTX.Operand.eval
#print axioms PtxTorchLean.Poisson.PTX.Op
#print axioms PtxTorchLean.Poisson.PTX.State.memory
#print axioms PtxTorchLean.Poisson.PTX.State.start
#print axioms PtxTorchLean.Poisson.PTX.State.bytes
#print axioms PtxTorchLean.Poisson.PTX.advance
#print axioms PtxTorchLean.Poisson.PTX.assign
#print axioms PtxTorchLean.Poisson.PTX.put
#print axioms PtxTorchLean.Poisson.PTX.Eval
#print axioms PtxTorchLean.Poisson.PTX.Step
#print axioms PtxTorchLean.Poisson.PTX.Runs
#print axioms PtxTorchLean.Poisson.PTX.Block
#print axioms PtxTorchLean.Poisson.PTX.eval_pc
#print axioms PtxTorchLean.Poisson.PTX.block_pc
#print axioms PtxTorchLean.Poisson.PTX.block_append
#print axioms PtxTorchLean.Poisson.PTX.block_fetched
#print axioms PtxTorchLean.Poisson.PTX.eval
#print axioms PtxTorchLean.Poisson.PTX.run
#print axioms PtxTorchLean.Poisson.PTX.eval_sound
#print axioms PtxTorchLean.Poisson.PTX.run_sound
#print axioms PtxTorchLean.Poisson.PTX.noFP
#print axioms PtxTorchLean.Poisson.PTX.eval_complete
#print axioms PtxTorchLean.Poisson.PTX.block_complete
#print axioms PtxTorchLean.Poisson.PTX.block_split
#print axioms PtxTorchLean.Poisson.PTX.wide
#print axioms PtxTorchLean.Poisson.PTX.address
#print axioms PtxTorchLean.Poisson.PTX.addressCode
#print axioms PtxTorchLean.Poisson.PTX.addressed
#print axioms PtxTorchLean.Poisson.PTX.loadCode
#print axioms PtxTorchLean.Poisson.PTX.storeCode
#print axioms PtxTorchLean.Poisson.PTX.addressed_memory
#print axioms PtxTorchLean.Poisson.PTX.addressed_globalStart
#print axioms PtxTorchLean.Poisson.PTX.addressed_sharedStart
#print axioms PtxTorchLean.Poisson.PTX.addressed_reg
#print axioms PtxTorchLean.Poisson.PTX.addressed_addr
#print axioms PtxTorchLean.Poisson.PTX.address_run
#print axioms PtxTorchLean.Poisson.PTX.run_append
#print axioms PtxTorchLean.Poisson.PTX.load_run
#print axioms PtxTorchLean.Poisson.PTX.store_run
#print axioms PtxTorchLean.Poisson.PTX.load_access_bound
#print axioms PtxTorchLean.Poisson.PTX.load_value
#print axioms PtxTorchLean.Poisson.PTX.load_block_eq
#print axioms PtxTorchLean.Poisson.PTX.store_block_eq
#print axioms PtxTorchLean.Poisson.PTX.Residual.code
#print axioms PtxTorchLean.Poisson.PTX.Residual.left
#print axioms PtxTorchLean.Poisson.PTX.Residual.right
#print axioms PtxTorchLean.Poisson.PTX.Residual.result
#print axioms PtxTorchLean.Poisson.PTX.Residual.finish
#print axioms PtxTorchLean.Poisson.PTX.Residual.executes
#print axioms PtxTorchLean.Poisson.PTX.Residual.correct
#print axioms PtxTorchLean.Poisson.PTX.Residual.fetched
#print axioms PtxTorchLean.Poisson.PTX.Kernel.Residual.prologue
#print axioms PtxTorchLean.Poisson.PTX.Kernel.Residual.program
#print axioms PtxTorchLean.Poisson.PTX.Kernel.Residual.index
#print axioms PtxTorchLean.Poisson.PTX.Kernel.Residual.setup
#print axioms PtxTorchLean.Poisson.PTX.Kernel.Residual.live
#print axioms PtxTorchLean.Poisson.PTX.Kernel.Residual.setup_live
#print axioms PtxTorchLean.Poisson.PTX.Kernel.Residual.setup_global
#print axioms PtxTorchLean.Poisson.PTX.Kernel.Residual.setup_shared
#print axioms PtxTorchLean.Poisson.PTX.Kernel.Residual.setup_bytes
#print axioms PtxTorchLean.Poisson.PTX.Kernel.Residual.setup_start
#print axioms PtxTorchLean.Poisson.PTX.Kernel.Residual.setup_index
#print axioms PtxTorchLean.Poisson.PTX.Kernel.Residual.setup_base
#print axioms PtxTorchLean.Poisson.PTX.Kernel.Residual.index_exact
#print axioms PtxTorchLean.Poisson.PTX.Kernel.Residual.prologue_live
#print axioms PtxTorchLean.Poisson.PTX.Kernel.Residual.correct
#print axioms PtxTorchLean.Poisson.PTX.Kernel.Residual.execution_exists
#print axioms PtxTorchLean.Poisson.PTX.Kernel.Residual.prologue_inactive
#print axioms PtxTorchLean.Poisson.PTX.Kernel.Residual.inactive
#print axioms PtxTorchLean.Poisson.PTX.Kernel.Residual.fetched_correct
#print axioms PtxTorchLean.Poisson.PTX.Kernel.Residual.fetched_exists
#print axioms PtxTorchLean.Poisson.PTX.Kernel.Residual.fetched_frame
#print axioms PtxTorchLean.Poisson.PTX.Kernel.Residual.fetched_inactive
#print axioms PtxTorchLean.Poisson.PTX.Kernel.Residual.view
#print axioms PtxTorchLean.Poisson.PTX.Kernel.Residual.torchlean_coordinate
#print axioms PtxTorchLean.Poisson.PTX.Text.register
#print axioms PtxTorchLean.Poisson.PTX.Text.operand
#print axioms PtxTorchLean.Poisson.PTX.Text.operation
#print axioms PtxTorchLean.Poisson.PTX.Text.space
#print axioms PtxTorchLean.Poisson.PTX.Text.data
#print axioms PtxTorchLean.Poisson.PTX.Text.instruction
#print axioms PtxTorchLean.Poisson.PTX.Text.residual

#print axioms PtxTorchLean.Poisson.PTX.Sources.Access
#print axioms PtxTorchLean.Poisson.PTX.Sources.Origin
#print axioms PtxTorchLean.Poisson.PTX.Sources.Compatible
#print axioms PtxTorchLean.Poisson.PTX.Sources.ReadOnly
#print axioms PtxTorchLean.Poisson.PTX.Sources.word_eq_of_bytes
#print axioms PtxTorchLean.Poisson.PTX.Sources.byte_read64
#print axioms PtxTorchLean.Poisson.PTX.Sources.read_only_initial
#print axioms PtxTorchLean.Poisson.PTX.Sources.read_only_value
#print axioms PtxTorchLean.Poisson.PTX.Sources.Disjoint
#print axioms PtxTorchLean.Poisson.PTX.Sources.readonly_of_disjoint
#print axioms PtxTorchLean.Poisson.PTX.Weak.data
#print axioms PtxTorchLean.Poisson.PTX.Weak.access
#print axioms PtxTorchLean.Poisson.PTX.Weak.instruction
#print axioms PtxTorchLean.Poisson.PTX.Weak.step
#print axioms PtxTorchLean.Poisson.PTX.Weak.execute
#print axioms PtxTorchLean.Poisson.PTX.Weak.access_origin
#print axioms PtxTorchLean.Poisson.PTX.Weak.data_pc
#print axioms PtxTorchLean.Poisson.PTX.Weak.Residual.accesses
#print axioms PtxTorchLean.Poisson.PTX.Weak.Residual.finish
#print axioms PtxTorchLean.Poisson.PTX.Weak.Residual.execution
#print axioms PtxTorchLean.Poisson.PTX.Weak.Residual.padding
#print axioms PtxTorchLean.Poisson.PTX.Weak.Residual.Parallel.Inputs
#print axioms PtxTorchLean.Poisson.PTX.Weak.Residual.Parallel.Inputs.addr
#print axioms PtxTorchLean.Poisson.PTX.Weak.Residual.Parallel.Candidate
#print axioms PtxTorchLean.Poisson.PTX.Weak.Residual.Parallel.characterize
#print axioms PtxTorchLean.Poisson.PTX.Weak.Residual.Parallel.events
#print axioms PtxTorchLean.Poisson.PTX.Weak.Residual.Parallel.trace_exact
#print axioms PtxTorchLean.Poisson.PTX.Weak.Residual.Parallel.store_origin
#print axioms PtxTorchLean.Poisson.PTX.Weak.Residual.Parallel.inputs_readonly
#print axioms PtxTorchLean.Poisson.PTX.Weak.Residual.Parallel.stored_value
#print axioms PtxTorchLean.Poisson.PTX.Weak.Residual.Parallel.publish
#print axioms PtxTorchLean.Poisson.PTX.Weak.Residual.Parallel.published_word
#print axioms PtxTorchLean.Poisson.PTX.Weak.Residual.Parallel.torchlean_output
#print axioms PtxTorchLean.Poisson.PTX.Weak.Residual.Parallel.canonical
#print axioms PtxTorchLean.Poisson.PTX.Weak.Residual.Parallel.witness
#print axioms PtxTorchLean.Poisson.PTX.Weak.Residual.Parallel.witness_sources
#print axioms PtxTorchLean.Poisson.PTX.Weak.Residual.Parallel.published_outside
#print axioms PtxTorchLean.Poisson.PTX.Weak.Residual.Parallel.Arena
#print axioms PtxTorchLean.Poisson.PTX.Weak.Residual.Parallel.Arena.context
#print axioms PtxTorchLean.Poisson.PTX.Weak.Residual.Parallel.Arena.start
#print axioms PtxTorchLean.Poisson.PTX.Weak.Residual.Parallel.Arena.index
#print axioms PtxTorchLean.Poisson.PTX.Weak.Residual.Parallel.Arena.live
#print axioms PtxTorchLean.Poisson.PTX.Weak.Residual.Parallel.Arena.inputs
#print axioms PtxTorchLean.Poisson.PTX.Weak.Residual.Parallel.Arena.addr
#print axioms PtxTorchLean.Poisson.PTX.Weak.Residual.Parallel.Arena.input_separation
#print axioms PtxTorchLean.Poisson.PTX.Weak.Residual.Parallel.Arena.output_ownership
#print axioms PtxTorchLean.Poisson.PTX.Weak.Residual.Parallel.Arena.correspondence
#print axioms PtxTorchLean.Poisson.PTX.Weak.Residual.Parallel.Checks.arena
#print axioms PtxTorchLean.Poisson.PTX.Weak.Residual.Parallel.Checks.memory
#print axioms PtxTorchLean.Poisson.PTX.Weak.Residual.Parallel.Checks.inputs
#print axioms PtxTorchLean.Poisson.PTX.Weak.Residual.Parallel.Checks.forward_order
#print axioms PtxTorchLean.Poisson.PTX.Weak.Residual.Parallel.Checks.reverse_order
#print axioms PtxTorchLean.Poisson.PTX.Weak.Residual.Parallel.Checks.badChoice
#print axioms PtxTorchLean.Poisson.PTX.Weak.Residual.Parallel.Checks.bad_candidate_executes
#print axioms PtxTorchLean.Poisson.PTX.Weak.Residual.Parallel.Checks.badEvents
#print axioms PtxTorchLean.Poisson.PTX.Weak.Residual.Parallel.Checks.bad_initial_source_rejected
#print axioms PtxTorchLean.Poisson.PTX.Weak.Residual.Parallel.Checks.output_cannot_source_input
#print axioms PtxTorchLean.Poisson.PTX.Weak.Residual.Parallel.Checks.overlapping_bytes
#print axioms PtxTorchLean.Poisson.PTX.Weak.Residual.Parallel.Checks.padding_has_no_access
#print axioms PtxTorchLean.Poisson.PTX.Weak.Residual.Parallel.Checks.tornEvents
#print axioms PtxTorchLean.Poisson.PTX.Weak.Residual.Parallel.Checks.tornSource
#print axioms PtxTorchLean.Poisson.PTX.Weak.Residual.Parallel.Checks.torn_sources_permitted

#print axioms PtxTorchLean.Poisson.PTX.Contraction.mac
#print axioms PtxTorchLean.Poisson.PTX.Contraction.term
#print axioms PtxTorchLean.Poisson.PTX.Contraction.terms
#print axioms PtxTorchLean.Poisson.PTX.Contraction.program
#print axioms PtxTorchLean.Poisson.PTX.Contraction.Accumulator
#print axioms PtxTorchLean.Poisson.PTX.Contraction.mac_correct
#print axioms PtxTorchLean.Poisson.PTX.Contraction.mac_exists
#print axioms PtxTorchLean.Poisson.PTX.Contraction.term_correct
#print axioms PtxTorchLean.Poisson.PTX.Contraction.term_exists
#print axioms PtxTorchLean.Poisson.PTX.Contraction.terms_correct
#print axioms PtxTorchLean.Poisson.PTX.Contraction.terms_exists
#print axioms PtxTorchLean.Poisson.PTX.Contraction.correct
#print axioms PtxTorchLean.Poisson.PTX.Contraction.exists_execution
#print axioms PtxTorchLean.Poisson.PTX.Contraction.Checks.memory4
#print axioms PtxTorchLean.Poisson.PTX.Contraction.Checks.state
#print axioms PtxTorchLean.Poisson.PTX.Contraction.Checks.a
#print axioms PtxTorchLean.Poisson.PTX.Contraction.Checks.b
#print axioms PtxTorchLean.Poisson.PTX.Contraction.Checks.matrix_coordinate
#print axioms PtxTorchLean.Poisson.PTX.Contraction.Checks.second_accumulator
#print axioms PtxTorchLean.Poisson.PTX.Contraction.Checks.outside_shared_rejected
#print axioms PtxTorchLean.Poisson.PTX.Contraction.Checks.unaligned_rejected
#print axioms PtxTorchLean.Poisson.PTX.Contraction.Checks.index_wrap
#print axioms PtxTorchLean.Poisson.PTX.Contraction.Checks.cancellation
#print axioms PtxTorchLean.Poisson.PTX.Contraction.Checks.cancellation_order
#print axioms PtxTorchLean.Poisson.PTX.Contraction.Checks.all_plans_have_eight_blocks
#print axioms PtxTorchLean.Poisson.PTX.Contraction.runs_pc_le
#print axioms PtxTorchLean.Poisson.PTX.Contraction.runs_eq_of_pc
#print axioms PtxTorchLean.Poisson.PTX.Contraction.fetched_block
#print axioms PtxTorchLean.Poisson.PTX.Contraction.leftTensor
#print axioms PtxTorchLean.Poisson.PTX.Contraction.rightTensor
#print axioms PtxTorchLean.Poisson.PTX.Contraction.tensor_fold
#print axioms PtxTorchLean.Poisson.PTX.Contraction.fetched_correct
#print axioms PtxTorchLean.Poisson.PTX.Contraction.fetched_exists
#print axioms PtxTorchLean.Poisson.PTX.Contraction.index_exact
#print axioms PtxTorchLean.Poisson.PTX.Contraction.location_exact
#print axioms PtxTorchLean.Poisson.PTX.Contraction.valid_of_matrix
#print axioms PtxTorchLean.Poisson.PTX.Contraction.Coord
#print axioms PtxTorchLean.Poisson.PTX.Contraction.Coord.operand
#print axioms PtxTorchLean.Poisson.PTX.Contraction.Matrix
#print axioms PtxTorchLean.Poisson.PTX.Contraction.indexWord
#print axioms PtxTorchLean.Poisson.PTX.Contraction.baseRegister
#print axioms PtxTorchLean.Poisson.PTX.Contraction.location
#print axioms PtxTorchLean.Poisson.PTX.Contraction.value
#print axioms PtxTorchLean.Poisson.PTX.Contraction.Valid
#print axioms PtxTorchLean.Poisson.PTX.Contraction.indexCode
#print axioms PtxTorchLean.Poisson.PTX.Contraction.loadCode
#print axioms PtxTorchLean.Poisson.PTX.Contraction.indexed
#print axioms PtxTorchLean.Poisson.PTX.Contraction.loaded
#print axioms PtxTorchLean.Poisson.PTX.Contraction.environment
#print axioms PtxTorchLean.Poisson.PTX.Contraction.Stable
#print axioms PtxTorchLean.Poisson.PTX.Contraction.stable_refl
#print axioms PtxTorchLean.Poisson.PTX.Contraction.stable_trans
#print axioms PtxTorchLean.Poisson.PTX.Contraction.stable_assign
#print axioms PtxTorchLean.Poisson.PTX.Contraction.stable_location
#print axioms PtxTorchLean.Poisson.PTX.Contraction.stable_valid
#print axioms PtxTorchLean.Poisson.PTX.Contraction.stable_value
#print axioms PtxTorchLean.Poisson.PTX.Contraction.wide_byte_offset
#print axioms PtxTorchLean.Poisson.PTX.Contraction.load_run
#print axioms PtxTorchLean.Poisson.PTX.Contraction.load_eq
#print axioms PtxTorchLean.Poisson.PTX.Contraction.loaded_reg
#print axioms PtxTorchLean.Poisson.PTX.Contraction.loaded_preserves
#print axioms PtxTorchLean.Poisson.PTX.Contraction.loaded_stable
#print axioms PtxTorchLean.Poisson.PTX.Contraction.Plan
#print axioms PtxTorchLean.Poisson.PTX.Contraction.plans
#print axioms PtxTorchLean.Poisson.PTX.Contraction.plans_accumulator
#print axioms PtxTorchLean.Poisson.PTX.Contraction.render
#print axioms PtxTorchLean.Poisson.PTX.Contraction.rendered
#print axioms PtxTorchLean.Poisson.PTX.mul32
#print axioms PtxTorchLean.Poisson.PTX.add32

#print axioms PtxTorchLean.Poisson.PTX.SharedStore.code
#print axioms PtxTorchLean.Poisson.PTX.SharedStore.location
#print axioms PtxTorchLean.Poisson.PTX.SharedStore.finish
#print axioms PtxTorchLean.Poisson.PTX.SharedStore.Valid
#print axioms PtxTorchLean.Poisson.PTX.SharedStore.run_store
#print axioms PtxTorchLean.Poisson.PTX.SharedStore.block_eq
#print axioms PtxTorchLean.Poisson.PTX.SharedStore.fetched_correct
#print axioms PtxTorchLean.Poisson.PTX.SharedStore.fetched_exists
#print axioms PtxTorchLean.Poisson.PTX.SharedStore.location_exact
#print axioms PtxTorchLean.Poisson.PTX.SharedStore.valid_of_plane
#print axioms PtxTorchLean.Poisson.PTX.SharedStore.keeps
#print axioms PtxTorchLean.Poisson.PTX.SharedStore.eval_keeps
#print axioms PtxTorchLean.Poisson.PTX.SharedStore.block_keeps
#print axioms PtxTorchLean.Poisson.PTX.SharedStore.contraction_keeps_lane
#print axioms PtxTorchLean.Poisson.PTX.SharedStore.contraction_valid
#print axioms PtxTorchLean.Poisson.PTX.SharedStore.contraction_store
#print axioms PtxTorchLean.Poisson.PTX.SharedStore.contraction_store_exists
#print axioms PtxTorchLean.Poisson.PTX.SharedStore.fetched_contraction_store
#print axioms PtxTorchLean.Poisson.PTX.SharedStore.fetched_contraction_store_exists
#print axioms PtxTorchLean.Poisson.PTX.SharedPlane.address
#print axioms PtxTorchLean.Poisson.PTX.SharedPlane.store_address
#print axioms PtxTorchLean.Poisson.PTX.SharedPlane.owners
#print axioms PtxTorchLean.Poisson.PTX.SharedPlane.planes_disjoint
#print axioms PtxTorchLean.Poisson.PTX.SharedPlane.publish
#print axioms PtxTorchLean.Poisson.PTX.SharedPlane.published_word
#print axioms PtxTorchLean.Poisson.PTX.SharedPlane.published_outside
#print axioms PtxTorchLean.Poisson.PTX.SharedPlane.order_independent
#print axioms PtxTorchLean.Poisson.PTX.SharedPlane.published_store
#print axioms PtxTorchLean.Poisson.PTX.SharedPlane.published_contraction
#print axioms PtxTorchLean.Poisson.PTX.SharedPlane.contraction_value
#print axioms PtxTorchLean.Poisson.PTX.SharedStore.Checks.state
#print axioms PtxTorchLean.Poisson.PTX.SharedStore.Checks.last_plane
#print axioms PtxTorchLean.Poisson.PTX.SharedStore.Checks.outside_rejected
#print axioms PtxTorchLean.Poisson.PTX.SharedStore.Checks.misaligned_rejected
#print axioms PtxTorchLean.Poisson.PTX.SharedStore.Checks.scratch_source
#print axioms PtxTorchLean.Poisson.PTX.SharedStore.Checks.bad_lane_rejected
#print axioms PtxTorchLean.Poisson.PTX.SharedStore.Checks.finals
#print axioms PtxTorchLean.Poisson.PTX.SharedStore.Checks.reversed_publication
#print axioms PtxTorchLean.Poisson.PTX.Contraction.renderedStores

#print axioms PtxTorchLean.Poisson.PTX.Concurrent.ordinary
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.data_pc
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.setLane
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.barrierConfig
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.barrierRequest
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.synchronize
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Step
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.waiting_blocks
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Aligned
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.setLane_aligned
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.synchronize_aligned
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.step_aligned
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.runs_aligned
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.History.activeKey
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.History.WaitingOrigin
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.History.CompleteOrigins
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.History.FreshCompletions
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.History.step_history
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.History.runs_history
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.History.completed_arrivals
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.History.arrival_position_spec
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.History.before_certificate
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.History.after_certificate
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.afterRound
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.roundPrefix
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.runs_append
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.barrier_round_exists
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.two_barriers_exist
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.missing_blocks_release
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.evaluate
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.evaluate_sound
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.tick
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.tick_sound
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.execute
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.execute_sound
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.store_origin
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.load_origin
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.padding_guard
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.active_guard
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.step_access_origin
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Visibility.Across
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Visibility.Compatible
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Visibility.Performed
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Visibility.SoleWriter
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Visibility.read_from_writer
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Visibility.across_arrivals
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Visibility.read_published
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Visibility.ownership_of_disjoint
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Checks.cfg
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Checks.seed
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Checks.start
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Checks.program
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Checks.schedule
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Checks.result
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Checks.successful
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Checks.executed
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Checks.actual_run
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Checks.history
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Checks.event_history
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Checks.ordered
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Checks.stale_candidate_exists
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Checks.stale_sources_rejected
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Checks.inactive_missing
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Checks.reuse
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Checks.block32
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Checks.state32
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Checks.last_padding_blocks
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Checks.fresh_compatible
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Checks.fresh_performed
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Checks.stale_compatible
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Checks.unique_writer
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Checks.actual_read_correct
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Checks.unsynchronized
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Checks.no_barrier_old_allowed

#print axioms PtxTorchLean.Poisson.PTX.Concurrent.padding_reaches_barrier
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.run_access_prefix

#print axioms PtxTorchLean.Poisson.PTX.Concurrent.release_aligned
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.StopsAt
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.step_crosses_barrier
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.crossed_barrier
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.access_after_barrier

#print axioms PtxTorchLean.Poisson.PTX.Concurrent.StopsFor
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.step_crosses_store
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.crossed_store
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.run_event_prefix
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.step_arrival_origin
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.store_before_arrival
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.access_after_barrier_index
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.producer_across

#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Forward
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.step_pc_mono
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.runs_pc_mono
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.run_access_bound
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.step_access_post
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.AccessOrder
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.step_access_order
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.run_access_order
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.access_site_unique
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.PlaneStores
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.plane_sole_writer
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.read_from_plane_producer

#print axioms PtxTorchLean.Poisson.PTX.Concurrent.ProducerChecks.forward
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.ProducerChecks.stops_writer
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.ProducerChecks.stops_barrier
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.ProducerChecks.padding_cannot_supply_store
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.ProducerChecks.bypass_rejected
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.ProducerChecks.every_schedule_order
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.ProducerChecks.site
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.ProducerChecks.sites_injective
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.ProducerChecks.plane_coverage
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.ProducerChecks.derived_read

#print axioms PtxTorchLean.Poisson.PTX.Concurrent.access_pc
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.access_single

#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Address.nextTag
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Address.tag
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Address.tag_zero
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Address.tag_next
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Address.Ready
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Address.Keeps
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Address.data_keeps
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Address.data_ready
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Address.Entries
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Address.Invariant
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Address.step_keeps
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Address.runs_keeps
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Address.step_invariant
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Address.runs_invariant

#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Padding.outside
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Padding.Boundaries
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Padding.Invariant
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Padding.step_invariant
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Padding.runs_invariant
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Padding.access_active

#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.planeOffset
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.dot
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.weighted
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.first
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.second
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.third
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.phase
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.code
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.site
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.checkAt
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Checked
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.checked_at
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.checked_keeps
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.checked_entries
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.checked_forward
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.checked_boundaries
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.checked_writer_stops
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.plane_stores
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.rendered

#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Checks.derivativeOffset
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Checks.weightOffset
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Checks.program
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Checks.q1
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Checks.q2
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Checks.q3
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Checks.q4
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Checks.checked
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Checks.sites_injective
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Checks.boundary
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Checks.preceding
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Checks.Bounded
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Checks.bounded_stops
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Checks.boundaries
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Checks.stores
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Checks.coverage
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Checks.unique
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Checks.publication
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Checks.wrong_scale_rejected
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Checks.jump_into_store_rejected

#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Witness.seed
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Witness.start
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Witness.cfg
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Witness.schedule
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Witness.candidate
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Witness.successful
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Witness.result
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Witness.executed
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Witness.candidate_run
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Witness.finished

#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Replay.view
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Replay.noStore
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Replay.operand_view
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Replay.view_assign
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Replay.view_memory
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Replay.view_start
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Replay.view_bytes
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Replay.ordinary_view
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Replay.data_view
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Replay.Slice
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Replay.Reads
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Replay.step_view
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Replay.run_view
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Replay.contraction
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Visibility.ReadOnly
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Visibility.read_only_initial
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Visibility.read_only_value
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Visibility.readonly_reads
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Replay.storePrefix
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Replay.stored_contraction
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Replay.published_contraction
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Inputs.SharedStores
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Inputs.shared_stores
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Inputs.store_space
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Inputs.global_readonly
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Inputs.nonzero_plane
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Inputs.input_readonly
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Inputs.initial_value
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Replay.Checks.two
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Replay.Checks.three
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Replay.Checks.six
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Replay.Checks.memory
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Replay.Checks.a
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Replay.Checks.b
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Replay.Checks.ops
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Replay.Checks.kernel
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Replay.Checks.seed
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Replay.Checks.start
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Replay.Checks.cfg
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Replay.Checks.schedule
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Replay.Checks.choose
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Replay.Checks.candidate
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Replay.Checks.result
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Replay.Checks.executed
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Replay.Checks.actual_run
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Replay.Checks.loadEvents
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Replay.Checks.events_exact
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Replay.Checks.compatible
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Replay.Checks.input_reads
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Replay.Checks.stored
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Replay.Checks.actual_store
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Replay.Checks.access
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Replay.Checks.store_record
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Replay.Checks.no_store_ops
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Replay.Checks.stored_tensor
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Replay.Checks.wrong_read_rejected

#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Symbolic.Bits
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Symbolic.Bits.eval
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Symbolic.Number
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Symbolic.Number.eval
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Symbolic.Value
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Symbolic.Registers
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Symbolic.Rel
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Symbolic.Matches
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Symbolic.add
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Symbolic.mul32
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Symbolic.add32
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Symbolic.wide
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Symbolic.eval_add
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Symbolic.eval_mul32
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Symbolic.eval_add32
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Symbolic.eval_wide
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Symbolic.operand
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Symbolic.number
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Symbolic.binary
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Symbolic.widening
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Symbolic.floating
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Symbolic.loaded
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Symbolic.data
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Symbolic.operand_sound
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Symbolic.number_sound
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Symbolic.binary_sound
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Symbolic.widening_sound
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Symbolic.floating_sound
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Symbolic.assign_sound
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Symbolic.data_sound
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Symbolic.Mode
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Symbolic.update
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Symbolic.transfer
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Symbolic.atPC
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Symbolic.at_zero
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Symbolic.at_next
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Symbolic.update_sound
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Symbolic.Guards
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Symbolic.Invariant
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Symbolic.Reads
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Symbolic.step_invariant
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Symbolic.runs_invariant
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Symbolic.access_registers
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric.seed
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric.address
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric.extract
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric.extract_sound
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric.loadCheck
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric.Loads
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric.entry
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric.sum
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric.expected
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric.Stores
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric.loads_q1
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric.loads_q2
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric.loads_q3
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric.loads_q4
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric.stores_q1
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric.stores_q2
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric.stores_q3
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric.stores_q4
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric.loads
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric.stores
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric.Launch
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric.Launch.aligned
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric.Launch.base_nat
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric.Launch.lane_nat
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric.Launch.symbolic
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric.guards
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric.access_active
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric.load_location
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.WordView.writesAt
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.WordView.stored
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.WordView.stored_eq
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.WordView.memory
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.WordView.global
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.WordView.input
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.WordView.output
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Geometry.split_offset
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Geometry.plane_zero
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Geometry.plane_positive
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric.view
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric.publication_view
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric.load_view
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric.all_reads
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric.value_invariant
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric.store_expression
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric.producer
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric.plane_expression
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric.grid
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric.entry_eval
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric.sum_fold
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric.sum_eval
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric.formula
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric.row_col
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric.expected_eval
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric.shared_word_address
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric.plane_equations
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric.target
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric.initialTensor
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric.global_grid
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric.input_grid
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric.compose
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric.completed_middle
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric.completed_store
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.ZeroSources.writes
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.ZeroSources.source
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.ZeroSources.Zero
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.ZeroSources.aligned
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.ZeroSources.compatible
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.ZeroSources.performed
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric.Checks.zero_words
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric.Checks.compatible
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric.Checks.performed
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric.Checks.launch
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric.Checks.witness_correspondence
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric.Checks.wrong_coordinate_rejected
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric.Checks.wrong_weight_rejected
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric.store_expression_of_reads
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.ZeroSources.evaluate_zero_reads
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.ZeroSources.tick_zero_reads
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.ZeroSources.execute_zero_reads
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric.Checks.decode_zero
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric.Checks.expected_zero

#print axioms PtxTorchLean.Poisson.PTX.CellFinal.left
#print axioms PtxTorchLean.Poisson.PTX.CellFinal.right
#print axioms PtxTorchLean.Poisson.PTX.CellFinal.arithmetic
#print axioms PtxTorchLean.Poisson.PTX.CellFinal.fold
#print axioms PtxTorchLean.Poisson.PTX.CellFinal.result
#print axioms PtxTorchLean.Poisson.PTX.CellFinal.Inputs
#print axioms PtxTorchLean.Poisson.PTX.CellFinal.inputs_stable
#print axioms PtxTorchLean.Poisson.PTX.CellFinal.contraction_keeps
#print axioms PtxTorchLean.Poisson.PTX.CellFinal.fold_stable
#print axioms PtxTorchLean.Poisson.PTX.CellFinal.arithmetic_correct
#print axioms PtxTorchLean.Poisson.PTX.CellFinal.arithmetic_exists
#print axioms PtxTorchLean.Poisson.PTX.CellFinal.Checks.initial
#print axioms PtxTorchLean.Poisson.PTX.CellFinal.Checks.start
#print axioms PtxTorchLean.Poisson.PTX.CellFinal.Checks.ctx
#print axioms PtxTorchLean.Poisson.PTX.CellFinal.Checks.code
#print axioms PtxTorchLean.Poisson.PTX.CellFinal.Checks.input_bounds
#print axioms PtxTorchLean.Poisson.PTX.CellFinal.Checks.store_bounds
#print axioms PtxTorchLean.Poisson.PTX.CellFinal.Checks.completed_value
#print axioms PtxTorchLean.Poisson.PTX.CellFinal.Checks.exists_fetched
#print axioms PtxTorchLean.Poisson.PTX.CellFinal.Checks.wrong_sum_changes_result
#print axioms PtxTorchLean.Poisson.PTX.CellFinal.Checks.short_output_rejected
#print axioms PtxTorchLean.Poisson.PTX.CellFinal.Checks.unaligned_output_rejected
#print axioms PtxTorchLean.Poisson.PTX.CellFinal.Checks.modular_index
#print axioms PtxTorchLean.Poisson.PTX.CellFinal.Checks.wrapped_extent_rejected
#print axioms PtxTorchLean.Poisson.PTX.CellFinal.index
#print axioms PtxTorchLean.Poisson.PTX.CellFinal.indexed
#print axioms PtxTorchLean.Poisson.PTX.CellFinal.location
#print axioms PtxTorchLean.Poisson.PTX.CellFinal.tail
#print axioms PtxTorchLean.Poisson.PTX.CellFinal.program
#print axioms PtxTorchLean.Poisson.PTX.CellFinal.location_stable
#print axioms PtxTorchLean.Poisson.PTX.CellFinal.tail_correct
#print axioms PtxTorchLean.Poisson.PTX.CellFinal.tail_exists
#print axioms PtxTorchLean.Poisson.PTX.CellFinal.correct
#print axioms PtxTorchLean.Poisson.PTX.CellFinal.execution_exists
#print axioms PtxTorchLean.Poisson.PTX.CellFinal.fetched_correct
#print axioms PtxTorchLean.Poisson.PTX.CellFinal.fetched_exists
#print axioms PtxTorchLean.Poisson.PTX.CellFinal.inputs_of_matrices
#print axioms PtxTorchLean.Poisson.PTX.CellFinal.index_exact
#print axioms PtxTorchLean.Poisson.PTX.CellFinal.location_exact
#print axioms PtxTorchLean.Poisson.PTX.CellFinal.output_valid
#print axioms PtxTorchLean.Poisson.PTX.CellFinal.wordBytes
#print axioms PtxTorchLean.Poisson.PTX.CellFinal.read_wordBytes
#print axioms PtxTorchLean.Poisson.PTX.CellFinal.phaseState
#print axioms PtxTorchLean.Poisson.PTX.CellFinal.phase_global
#print axioms PtxTorchLean.Poisson.PTX.CellFinal.phase_shared
#print axioms PtxTorchLean.Poisson.PTX.CellFinal.phase_result
#print axioms PtxTorchLean.Poisson.PTX.CellFinal.completed_from_middle
#print axioms PtxTorchLean.Poisson.PTX.CellFinal.bases
#print axioms PtxTorchLean.Poisson.PTX.CellFinal.words
#print axioms PtxTorchLean.Poisson.PTX.CellFinal.grid
#print axioms PtxTorchLean.Poisson.PTX.CellFinal.value_grid
#print axioms PtxTorchLean.Poisson.PTX.CellFinal.fold_fin
#print axioms PtxTorchLean.Poisson.PTX.CellFinal.fold_product
#print axioms PtxTorchLean.Poisson.PTX.CellFinal.result_tensor
#print axioms PtxTorchLean.Poisson.PTX.CellFinal.rendered
#print axioms PtxTorchLean.Poisson.PTX.CellFinal.exists_from_middle

#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Extension.run_append_code
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Extension.ReadOnly
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Extension.prefix_store
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Extension.compatible_prefix
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Extension.performed_prefix
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Extension.view_append
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Checks.schedule
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Checks.candidate
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Checks.successful
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Checks.result
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Checks.executed
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Checks.tail_run
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Checks.finished
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Checks.whole_run
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Checks.zero_words
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Checks.compatible
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Checks.performed
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Checks.correspondence
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Checks.wrong_join_rejected
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.expected_tensor
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.completed_arithmetic
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.stored_local
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.tail_completion
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.body
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.suffix
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.program
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.checked
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.shared_stores
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.sites
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.boundaries
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.stores
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.no_tail_stores
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.expected
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Results
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.results
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.loadCheck
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Loads
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.loads
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.guards
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.symbolic
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.coverage
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.unique
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.publication
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.active
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.load_location
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.load_view
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.combined
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.tail_late
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.tail_readonly
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.all_reads
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.register_value

#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Cut.crossing_state
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Cut.step_prefix
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Cut.split_run

#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.split
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.completed_run
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.stored_run

#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Projection.Embedding
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Projection.Retained
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Projection.Separated
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Projection.source
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Projection.observed
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Projection.compatible
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Projection.across
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Projection.performed
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Projection.separated_by_fence
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Projection.Checks.key
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Projection.Checks.write
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Projection.Checks.read
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Projection.Checks.small
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Projection.Checks.large
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Projection.Checks.embedding
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Projection.Checks.original
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Projection.Checks.whole_compatible
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Projection.Checks.whole_performed
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Projection.Checks.separated
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Projection.Checks.retained_compatible
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Projection.Checks.retained_performed
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Projection.Checks.renamed_source
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Projection.Checks.ordered
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Projection.Checks.overlapping
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Projection.Checks.badEmbedding
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Projection.Checks.overlap_rejected
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Coefficients.extent
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Coefficients.checkAt
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Coefficients.Checked
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Coefficients.checked
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Coefficients.read_bounds
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Output.after_coefficients
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Output.fetched_preserves_coefficients
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Output.distinct_outputs
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Output.projected_arithmetic

#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Projection.empty
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Projection.drop
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Projection.keep
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Projection.Omitted
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Projection.omitted_keep
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Projection.omitted_drop

#print axioms PtxTorchLean.Poisson.PTX.Concurrent.WithTail.State
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.WithTail.Outcome
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.WithTail.lane
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.WithTail.update
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.WithTail.access
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.WithTail.Step
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.WithTail.Runs
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.WithTail.halted_blocks
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.WithTail.step_aligned
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.WithTail.keeps
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.WithTail.eval_keeps
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.WithTail.clip
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.WithTail.Related
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.WithTail.related_refl
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.WithTail.related_live
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.WithTail.related_update

#print axioms PtxTorchLean.Poisson.PTX.Concurrent.WithTail.synchronize_related
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.WithTail.front_step

#print axioms PtxTorchLean.Poisson.PTX.Concurrent.WithTail.tail_related
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.WithTail.project_filtered
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.WithTail.project

#print axioms PtxTorchLean.Poisson.PTX.Concurrent.WithTail.tick
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.WithTail.tick_sound
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.WithTail.execute
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.WithTail.execute_sound

#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.redirect
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.front
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.tail_length
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.front_length
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Bounded
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.bounded
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.clipped
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.tail_keeps
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.padding_return
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.arithmetic
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.OutputEvent
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.tail_events
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.arithmetic_filtered

#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.result_under_store_bounds

#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Checks.start
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Checks.ctx
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Checks.schedule
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Checks.candidate
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Checks.successful
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Checks.result
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Checks.executed
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Checks.actual_run
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Checks.returned
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Checks.padding_did_not_store
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Checks.four_outputs
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Checks.interleaved
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Checks.stopped_again
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Checks.projected

#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Checks.eventCheck
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Checks.event_facts
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Checks.facts_at
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Checks.compatible
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Checks.performed
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Checks.launch
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Checks.correspondence

#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Address.scaled
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Address.Ready
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Address.ready_before
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Address.tail_ready

#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Address.fact
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Address.Checked
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Address.checked
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Address.front_keeps
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Address.tail_keeps_register
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Address.location_eq
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Address.Invariant
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Address.front_ready
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Address.step_ready
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Address.runs_ready

#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Address.step_keeps
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Address.runs_keeps
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Address.runs_location
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Address.initial_ready
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Address.stored_word

#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Address.access_prefix
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Address.tail_address
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Address.step_address
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Address.store_address

#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.OutputBounds
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.store_bounds
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.coefficient_nowrap
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.result_from_launch
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.stored_from_launch

#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.output_disjoint
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.stores_disjoint

#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.AddressChecks.launch_bounds
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.AddressChecks.stored
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.AddressChecks.index_wrap_rejected
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.AddressChecks.address_wrap_rejected
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.AddressChecks.sample
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.AddressChecks.cfg
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.AddressChecks.ctx
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.AddressChecks.sampleRun
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.AddressChecks.sampleResult
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.AddressChecks.sample_executed
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.AddressChecks.sample_actual
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.AddressChecks.nonzero_store

#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Publication.step_after
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Publication.runs_after
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Publication.step_value
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Publication.store_value
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Publication.Wrote
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Publication.front_before_store
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Publication.step_without_store
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Publication.runs_without_store
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Publication.completed_wrote
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.GlobalPublication.applyEvent
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.GlobalPublication.publish
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.GlobalPublication.Safe
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.GlobalPublication.Present
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.GlobalPublication.apply_preserves
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.GlobalPublication.preserves
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.GlobalPublication.word
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.GlobalPublication.permuted_word
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.GlobalPublication.outside
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Publication.safe_records
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Publication.present_record
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Publication.published_word
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Publication.published_outside
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Publication.tensor
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Publication.location_entry
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Publication.published_entry
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Publication.published_tensor
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.PublicationChecks.cells
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.PublicationChecks.tensor_output
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.PublicationChecks.reversed_output
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.PublicationChecks.nonzero_publication
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.PublicationChecks.missing_store_rejected
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.PublicationChecks.overlapping_store_rejected
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.PublicationChecks.coefficient_bytes_preserved

#print axioms PtxTorchLean.Poisson.PTX.CellPrologue.Context
#print axioms PtxTorchLean.Poisson.PTX.CellPrologue.Source
#print axioms PtxTorchLean.Poisson.PTX.CellPrologue.Context.value
#print axioms PtxTorchLean.Poisson.PTX.CellPrologue.Instr
#print axioms PtxTorchLean.Poisson.PTX.CellPrologue.State
#print axioms PtxTorchLean.Poisson.PTX.CellPrologue.assign
#print axioms PtxTorchLean.Poisson.PTX.CellPrologue.eval
#print axioms PtxTorchLean.Poisson.PTX.CellPrologue.Step
#print axioms PtxTorchLean.Poisson.PTX.CellPrologue.Runs
#print axioms PtxTorchLean.Poisson.PTX.CellPrologue.execute
#print axioms PtxTorchLean.Poisson.PTX.CellPrologue.execute_sound
#print axioms PtxTorchLean.Poisson.PTX.CellPrologue.execute_complete
#print axioms PtxTorchLean.Poisson.PTX.CellPrologue.program
#print axioms PtxTorchLean.Poisson.PTX.CellPrologue.finish
#print axioms PtxTorchLean.Poisson.PTX.CellPrologue.execution
#print axioms PtxTorchLean.Poisson.PTX.CellPrologue.fetched_exists
#print axioms PtxTorchLean.Poisson.PTX.CellPrologue.fetched_correct
#print axioms PtxTorchLean.Poisson.PTX.CellPrologue.memories
#print axioms PtxTorchLean.Poisson.PTX.CellPrologue.other_register
#print axioms PtxTorchLean.Poisson.PTX.CellPrologue.Ready
#print axioms PtxTorchLean.Poisson.PTX.CellPrologue.ready
#print axioms PtxTorchLean.Poisson.PTX.CellPrologue.coordinates
#print axioms PtxTorchLean.Poisson.PTX.CellPrologue.threadContext
#print axioms PtxTorchLean.Poisson.PTX.CellPrologue.thread_registers
#print axioms PtxTorchLean.Poisson.PTX.CellPrologue.render
#print axioms PtxTorchLean.Poisson.PTX.CellPrologue.rendered
#print axioms PtxTorchLean.Poisson.PTX.CellPrologue.Checks.start
#print axioms PtxTorchLean.Poisson.PTX.CellPrologue.Checks.ctx
#print axioms PtxTorchLean.Poisson.PTX.CellPrologue.Checks.all_lanes
#print axioms PtxTorchLean.Poisson.PTX.CellPrologue.Checks.zero_width_unsupported
#print axioms PtxTorchLean.Poisson.PTX.CellPrologue.Checks.wrong_pc_rejected
#print axioms PtxTorchLean.Poisson.PTX.CellPrologue.Checks.row_mutation_rejected
#print axioms PtxTorchLean.Poisson.PTX.CellPrologue.Checks.wrong_guard_rejected
#print axioms PtxTorchLean.Poisson.PTX.CellPrologue.Checks.high_unsigned_lane

#print axioms PtxTorchLean.Poisson.PTX.read32
#print axioms PtxTorchLean.Poisson.PTX.write32
#print axioms PtxTorchLean.Poisson.PTX.Valid32
#print axioms PtxTorchLean.Poisson.PTX.write32_outside
#print axioms PtxTorchLean.Poisson.PTX.read32_write32_disjoint
#print axioms PtxTorchLean.Poisson.PTX.read32_write64_disjoint
#print axioms PtxTorchLean.Poisson.PTX.address32
#print axioms PtxTorchLean.Poisson.PTX.address32_exact
#print axioms PtxTorchLean.Poisson.PTX.valid32_of_array
#print axioms PtxTorchLean.Poisson.PTX.Indexed.Instr
#print axioms PtxTorchLean.Poisson.PTX.Indexed.mad
#print axioms PtxTorchLean.Poisson.PTX.Indexed.wide
#print axioms PtxTorchLean.Poisson.PTX.Indexed.Eval
#print axioms PtxTorchLean.Poisson.PTX.Indexed.eval
#print axioms PtxTorchLean.Poisson.PTX.Indexed.noFP
#print axioms PtxTorchLean.Poisson.PTX.Indexed.Block
#print axioms PtxTorchLean.Poisson.PTX.Indexed.Step
#print axioms PtxTorchLean.Poisson.PTX.Indexed.Runs
#print axioms PtxTorchLean.Poisson.PTX.Indexed.run
#print axioms PtxTorchLean.Poisson.PTX.Indexed.eval_sound
#print axioms PtxTorchLean.Poisson.PTX.Indexed.eval_complete
#print axioms PtxTorchLean.Poisson.PTX.Indexed.eval_pc
#print axioms PtxTorchLean.Poisson.PTX.Indexed.run_sound
#print axioms PtxTorchLean.Poisson.PTX.Indexed.run_complete
#print axioms PtxTorchLean.Poisson.PTX.Indexed.block_pc
#print axioms PtxTorchLean.Poisson.PTX.Indexed.block_fetched
#print axioms PtxTorchLean.Poisson.PTX.Indexed.runs_pc_le
#print axioms PtxTorchLean.Poisson.PTX.Indexed.runs_eq_of_pc
#print axioms PtxTorchLean.Poisson.PTX.Indexed.fetched_block
#print axioms PtxTorchLean.Poisson.PTX.CellGather.code
#print axioms PtxTorchLean.Poisson.PTX.CellGather.index
#print axioms PtxTorchLean.Poisson.PTX.CellGather.connectivityAddress
#print axioms PtxTorchLean.Poisson.PTX.CellGather.node
#print axioms PtxTorchLean.Poisson.PTX.CellGather.sourceAddress
#print axioms PtxTorchLean.Poisson.PTX.CellGather.value
#print axioms PtxTorchLean.Poisson.PTX.CellGather.destination
#print axioms PtxTorchLean.Poisson.PTX.CellGather.Valid
#print axioms PtxTorchLean.Poisson.PTX.CellGather.finish
#print axioms PtxTorchLean.Poisson.PTX.CellGather.execution
#print axioms PtxTorchLean.Poisson.PTX.CellGather.correct
#print axioms PtxTorchLean.Poisson.PTX.CellGather.stored
#print axioms PtxTorchLean.Poisson.PTX.CellGather.registers
#print axioms PtxTorchLean.Poisson.PTX.CellGather.fetched_correct
#print axioms PtxTorchLean.Poisson.PTX.CellGather.fetched_exists
#print axioms PtxTorchLean.Poisson.PTX.CellGather.index_exact
#print axioms PtxTorchLean.Poisson.PTX.CellGather.Layout
#print axioms PtxTorchLean.Poisson.PTX.CellGather.index_inside
#print axioms PtxTorchLean.Poisson.PTX.CellGather.connectivity_address
#print axioms PtxTorchLean.Poisson.PTX.CellGather.node_inside
#print axioms PtxTorchLean.Poisson.PTX.CellGather.valid_of_layout
#print axioms PtxTorchLean.Poisson.PTX.CellGather.render
#print axioms PtxTorchLean.Poisson.PTX.CellGather.rendered
#print axioms PtxTorchLean.Poisson.PTX.CellGather.Checks.start
#print axioms PtxTorchLean.Poisson.PTX.CellGather.Checks.addresses
#print axioms PtxTorchLean.Poisson.PTX.CellGather.Checks.bits_copied
#print axioms PtxTorchLean.Poisson.PTX.CellGather.Checks.four_byte_extent
#print axioms PtxTorchLean.Poisson.PTX.CellGather.Checks.unaligned_rejected
#print axioms PtxTorchLean.Poisson.PTX.CellGather.Checks.truncated_index_rejected
#print axioms PtxTorchLean.Poisson.PTX.CellGather.Checks.invalid_node_rejected
#print axioms PtxTorchLean.Poisson.PTX.CellGather.Checks.neighboring_index
#print axioms PtxTorchLean.Poisson.PTX.CellGather.Checks.mixed_overlap_rejected
#print axioms PtxTorchLean.Poisson.PTX.CellGather.torchlean

#print axioms PtxTorchLean.Poisson.gather

#print axioms PtxTorchLean.Poisson.PTX.write32_at
#print axioms PtxTorchLean.Poisson.PTX.read32_write32

#print axioms PtxTorchLean.Poisson.PTX.IndexSources.Access
#print axioms PtxTorchLean.Poisson.PTX.IndexSources.byte32
#print axioms PtxTorchLean.Poisson.PTX.IndexSources.byte_read32
#print axioms PtxTorchLean.Poisson.PTX.IndexSources.word_eq_of_bytes
#print axioms PtxTorchLean.Poisson.PTX.IndexSources.Compatible
#print axioms PtxTorchLean.Poisson.PTX.IndexSources.ReadOnly
#print axioms PtxTorchLean.Poisson.PTX.IndexSources.read_only_initial
#print axioms PtxTorchLean.Poisson.PTX.IndexSources.read_only_value
#print axioms PtxTorchLean.Poisson.PTX.IndexSources.readonly_of_disjoint
#print axioms PtxTorchLean.Poisson.PTX.IndexSources.readonly_of_no_global_stores
#print axioms PtxTorchLean.Poisson.PTX.Indexed.Candidate.Data
#print axioms PtxTorchLean.Poisson.PTX.Indexed.Candidate.noGlobalStore
#print axioms PtxTorchLean.Poisson.PTX.Indexed.Candidate.noSharedLoad
#print axioms PtxTorchLean.Poisson.PTX.Indexed.Candidate.data_pc
#print axioms PtxTorchLean.Poisson.PTX.Indexed.Candidate.data_global
#print axioms PtxTorchLean.Poisson.PTX.Indexed.Candidate.store_shared
#print axioms PtxTorchLean.Poisson.PTX.Indexed.Candidate.load_global
#print axioms PtxTorchLean.Poisson.PTX.Indexed.Candidate.replay
#print axioms PtxTorchLean.Poisson.PTX.Indexed.Candidate.Block
#print axioms PtxTorchLean.Poisson.PTX.Indexed.Candidate.block_global
#print axioms PtxTorchLean.Poisson.PTX.Indexed.Candidate.block_store_shared
#print axioms PtxTorchLean.Poisson.PTX.Indexed.Candidate.block_replay
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Instr
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.program
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.State
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Outcome
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.lane
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.setLane
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.synchronize
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Dispatch
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Step
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Runs
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.program_length
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.barrier_fetch
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.step_aligned
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.runs_aligned
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.waiting_blocks
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.setup_pc
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.setup_global
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.gather_member
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.gather_safe
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.gather_plain
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.step_no_global_store
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.no_global_store
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.step_global
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.runs_global
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.index_value
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.word_value
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Local.eval
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Local.Step
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Local.Runs
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Local.trans
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Local.deterministic
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Local.terminal_unique
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Local.prologue
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Local.gather
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Local.beforeGather
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Local.finish
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Local.exists_trace
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Words
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Indices
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.step_local
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.runs_local
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.actual_trace
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Local.finish_pc
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.completed_lane
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.gathered_bits
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.gathered_torchlean
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.skip_target
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.crossing
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.terminal
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.terminal_runs
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.completed_barrier
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Local.finish_register
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.resume
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.arithmetic_launch
#print axioms PtxTorchLean.Poisson.PTX.Indexed.Candidate.evaluate
#print axioms PtxTorchLean.Poisson.PTX.Indexed.Candidate.evaluate_sound
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.tick
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.tick_sound
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.execute
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.execute_sound
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Checks.memory
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Checks.seed
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Checks.start
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Checks.cfg
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Checks.bases
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Checks.ctx
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Checks.kernel
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Checks.choose
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Checks.schedule
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Checks.candidate
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Checks.result
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Checks.executed
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Checks.actual_run
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Checks.completed
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Checks.gathered
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Checks.padding_untouched
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Checks.no_early_release
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Checks.unsigned_index_overlap
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Checks.initial
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Checks.wordsInitial
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Checks.indicesInitial
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Checks.sources_checked
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Checks.compatible
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Checks.index_compatible
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Checks.wrong_index_rejected
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Checks.launch_from_execution
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.label
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.render
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.rendered

#print axioms PtxTorchLean.Poisson.PTX.CellEntry.store_instruction
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.store_origin
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.contents
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.step_after_store
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.runs_after_store
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.recorded_store
#print axioms PtxTorchLean.Poisson.PTX.Indexed.block_split
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Local.Avoid
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Local.cannot_avoid
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Local.reaches_store
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Wrote
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.store_fetch
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.missing_stutters
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.local_store_not_self
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.avoid_missing
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.completed_wrote
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Local.Avoid.trans
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Local.prologue_avoids
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Local.padding_avoids
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.recorded_path
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.store_active
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.context_lane
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.destination_context
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.destination_address
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.recorded_gather
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Producers.value
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Producers.info
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Producers.producer
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Producers.byte_owner
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Producers.different_writers
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.ProducerChecks.aligned
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.ProducerChecks.valid
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.ProducerChecks.actual_producer
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.ProducerChecks.padding_has_no_store
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.ProducerChecks.independent_slots
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.recorded_torchlean

#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Visibility.read_from_value
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.step_history
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.runs_history
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.completed_arrivals
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.run_event_prefix
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.arrival_origin
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.no_store_after
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.store_before_arrival
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.store_before_completion
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Producers.read_gathered
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.no_access_zero
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.preserves_gather
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.preserves_gather
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.continuation
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.continuation_read
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.VisibilityChecks.key
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.VisibilityChecks.completion
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.VisibilityChecks.ordered_producers
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.VisibilityChecks.read
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.VisibilityChecks.observed_value
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.VisibilityChecks.stale_read_rejected
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.History.append_complete
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.History.synchronize_history
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.History.ordinary_history

#print axioms PtxTorchLean.Poisson.PTX.Concurrent.SourceCut.Covered
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.SourceCut.Published
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.SourceCut.source
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.SourceCut.Ordered
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.SourceCut.Separate
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.SourceCut.left
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.SourceCut.right
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.SourceCut.across
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.SourceCut.initial_unchanged
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.SourceCut.compatible
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.SourceCut.across_right
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.SourceCut.performed
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.SourceCheck.byteCompatible
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.SourceCheck.Checked
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.SourceCheck.sound
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.publication
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.publication_lane
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.publication_word
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.publication_sound
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.publication_ordered
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.before_ids
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.publication_torchlean
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.body_sources
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.body_result
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.continued_cell
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.published_result
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.cell_result
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.cell_tensor
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.RebaseChecks.bodyStart
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.RebaseChecks.bodyContext
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.RebaseChecks.choose
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.RebaseChecks.candidate
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.RebaseChecks.bodyResult
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.RebaseChecks.executed
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.RebaseChecks.actual_body
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.RebaseChecks.reads
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.RebaseChecks.whole
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.RebaseChecks.sources
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.RebaseChecks.checked
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.RebaseChecks.compatible
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.RebaseChecks.shared_read_at
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.RebaseChecks.performed
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.RebaseChecks.snapshot_sound
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.RebaseChecks.rebased_sources
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.RebaseChecks.cross_lane_read

#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Control.Ready
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Control.initial
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Control.later
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Control.setup
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Control.preserves
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Control.preserves_data
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Control.gather_preserves
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Control.gather
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Control.gather_past
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Control.skip_pc
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Control.sync_pc
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Control.step
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Control.from_run
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Control.launch
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Control.Active
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Control.active_initial
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Control.setup_pc
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Control.setup_next
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Control.active_step
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Control.active_run
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Control.live_gather
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Control.indexWord
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Control.indexScale
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Control.IndexReady
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Control.index_initial
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Control.index_outside
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Control.gather_index
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Control.index_step
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Control.index_run
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Control.InputLayout
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Control.index_nat
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Control.index_address
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Control.index_below
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Control.output_fence
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Control.index_instruction
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Control.index_origin
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Control.index_step_bound
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Control.index_bounds
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Control.joint_indices
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Control.indices_compatible
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Control.nodeWord
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Control.sourceScale
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Control.SourceReady
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Control.source_initial
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Control.source_outside
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Control.gather_source
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Control.source_step
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Control.source_below
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Control.word_instruction
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Control.word_origin
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Control.word_step_bound
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Control.word_bounds
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Control.joint_words
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Control.InputLayout.of_gather
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.Control.joint_sources
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.joint_cell_tensor
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.JointChecks.inputs
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.JointChecks.joint_indices
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.JointChecks.derived_prefix
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.JointChecks.overlapping_output_rejected

#print axioms PtxTorchLean.Poisson.PTX.Relocate.scalar
#print axioms PtxTorchLean.Poisson.PTX.Relocate.scalar_pc
#print axioms PtxTorchLean.Poisson.PTX.Relocate.scalar_regs
#print axioms PtxTorchLean.Poisson.PTX.Relocate.operand
#print axioms PtxTorchLean.Poisson.PTX.Relocate.scalar_advance
#print axioms PtxTorchLean.Poisson.PTX.Relocate.scalar_assign
#print axioms PtxTorchLean.Poisson.PTX.Relocate.scalar_put
#print axioms PtxTorchLean.Poisson.PTX.Relocate.memory
#print axioms PtxTorchLean.Poisson.PTX.Relocate.start
#print axioms PtxTorchLean.Poisson.PTX.Relocate.bytes
#print axioms PtxTorchLean.Poisson.PTX.Relocate.eval
#print axioms PtxTorchLean.Poisson.PTX.Relocate.access
#print axioms PtxTorchLean.Poisson.PTX.Relocate.key
#print axioms PtxTorchLean.Poisson.PTX.Relocate.barrierEvent
#print axioms PtxTorchLean.Poisson.PTX.Relocate.event
#print axioms PtxTorchLean.Poisson.PTX.Relocate.core
#print axioms PtxTorchLean.Poisson.PTX.Relocate.outcome
#print axioms PtxTorchLean.Poisson.PTX.Relocate.key_injective
#print axioms PtxTorchLean.Poisson.PTX.Relocate.data
#print axioms PtxTorchLean.Poisson.PTX.Relocate.barrierConfig
#print axioms PtxTorchLean.Poisson.PTX.Relocate.request
#print axioms PtxTorchLean.Poisson.PTX.Relocate.barrierResult
#print axioms PtxTorchLean.Poisson.PTX.Relocate.barrier_step
#print axioms PtxTorchLean.Poisson.PTX.Relocate.core_lane
#print axioms PtxTorchLean.Poisson.PTX.Relocate.core_barrier
#print axioms PtxTorchLean.Poisson.PTX.Relocate.core_site
#print axioms PtxTorchLean.Poisson.PTX.Relocate.core_setLane
#print axioms PtxTorchLean.Poisson.PTX.Relocate.shifted_config
#print axioms PtxTorchLean.Poisson.PTX.Relocate.shifted_request
#print axioms PtxTorchLean.Poisson.PTX.Relocate.synchronize
#print axioms PtxTorchLean.Poisson.PTX.Relocate.instruction
#print axioms PtxTorchLean.Poisson.PTX.Relocate.dispatch
#print axioms PtxTorchLean.Poisson.PTX.Relocate.eval_back
#print axioms PtxTorchLean.Poisson.PTX.Relocate.data_back
#print axioms PtxTorchLean.Poisson.PTX.Relocate.scalar_injective
#print axioms PtxTorchLean.Poisson.PTX.Relocate.core_injective
#print axioms PtxTorchLean.Poisson.PTX.Relocate.dispatch_back
#print axioms PtxTorchLean.Poisson.PTX.Relocate.kernel
#print axioms PtxTorchLean.Poisson.PTX.Relocate.kernel_simple
#print axioms PtxTorchLean.Poisson.PTX.Relocate.kernel_eval
#print axioms PtxTorchLean.Poisson.PTX.Relocate.kernel_back
#print axioms PtxTorchLean.Poisson.PTX.Relocate.tailState
#print axioms PtxTorchLean.Poisson.PTX.Relocate.tailOutcome
#print axioms PtxTorchLean.Poisson.PTX.Relocate.tail_lane
#print axioms PtxTorchLean.Poisson.PTX.Relocate.tail_update
#print axioms PtxTorchLean.Poisson.PTX.Relocate.tail_access
#print axioms PtxTorchLean.Poisson.PTX.Relocate.tailState_injective
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.AtOffset.Step
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.AtOffset.Runs
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.AtOffset.aligned
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.AtOffset.step_forward
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.AtOffset.step_back
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.AtOffset.run_forward
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.AtOffset.run_back
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.entry
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.entryState
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.Outcome
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.Step
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.Runs
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.step_aligned
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.before
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.split
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.ready_view
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.body_run
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.executions
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Relabel.EventRelated
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Relabel.at_old
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Relabel.at_new
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Relabel.compatible
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Relabel.across
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Relabel.performed
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Relabel.indices
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Clock.Before
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Clock.generation
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Clock.monotone
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Clock.carry
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Clock.emitted
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Clock.before_reset
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Clock.Progress
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Clock.Progress.refl
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Clock.Progress.trans
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Clock.unchanged
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Clock.sync_barrier
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Clock.sync_events
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Clock.sync_progress
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Clock.dispatch_progress
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.clock_step
#print axioms PtxTorchLean.Poisson.PTX.CellEntry.clock_run
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.WithTail.clock_step
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.WithTail.clock_run
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Relabel.renameAfter
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Relabel.before_event
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Relabel.after_event
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Relabel.before_history
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Relabel.after_history
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Relabel.joined
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.histories
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.sources
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Relabel.published
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.GlobalPublication.append
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.GlobalPublication.no_stores
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.OutputLayout
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.output_bounds
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.tensor
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.begin
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.append
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.prefix_run
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.offset_run
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.compose
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.Checks.events
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.Checks.final
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.Checks.actual
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.Checks.shifted_reads
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.Checks.native_pc
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.Checks.checked
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.Checks.admitted
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.Checks.extracted
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.Checks.barrier_sites
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.Zero.seed
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.Zero.start
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.Zero.cfg
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.Zero.bases
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.Zero.prefixCandidate
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.Zero.prefixResult
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.Zero.prefix_executed
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.Zero.ctx
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.Zero.bodyStart
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.Zero.bodyCandidate
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.Zero.bodyResult
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.Zero.body_executed
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.Zero.events
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.Zero.final
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.Zero.actual
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.Zero.returned
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.Zero.four_outputs
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.Zero.zero
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.Zero.admitted
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.Zero.aligned
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.Zero.performed
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.Zero.indices_admitted
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.shape

#print axioms PtxTorchLean.Poisson.PTX.CoefficientRepresentation.rows
#print axioms PtxTorchLean.Poisson.PTX.CoefficientRepresentation.square
#print axioms PtxTorchLean.Poisson.PTX.CoefficientRepresentation.get_rows
#print axioms PtxTorchLean.Poisson.PTX.CoefficientRepresentation.get_square
#print axioms PtxTorchLean.Poisson.PTX.CoefficientRepresentation.local_action
#print axioms PtxTorchLean.Poisson.PTX.CoefficientRepresentation.Represents
#print axioms PtxTorchLean.Poisson.PTX.CoefficientRepresentation.tensor_ext
#print axioms PtxTorchLean.Poisson.PTX.CoefficientRepresentation.tensors
#print axioms PtxTorchLean.Poisson.PTX.CoefficientRepresentation.calculation
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.operator_tensor
#print axioms PtxTorchLean.Poisson.PTX.Flow.Compare
#print axioms PtxTorchLean.Poisson.PTX.Flow.Compare.apply
#print axioms PtxTorchLean.Poisson.PTX.Flow.Source
#print axioms PtxTorchLean.Poisson.PTX.Flow.source
#print axioms PtxTorchLean.Poisson.PTX.Flow.Instr
#print axioms PtxTorchLean.Poisson.PTX.Flow.State
#print axioms PtxTorchLean.Poisson.PTX.Flow.next
#print axioms PtxTorchLean.Poisson.PTX.Flow.halt
#print axioms PtxTorchLean.Poisson.PTX.Flow.goto
#print axioms PtxTorchLean.Poisson.PTX.Flow.simple
#print axioms PtxTorchLean.Poisson.PTX.Flow.Eval
#print axioms PtxTorchLean.Poisson.PTX.Flow.Step
#print axioms PtxTorchLean.Poisson.PTX.Flow.Runs
#print axioms PtxTorchLean.Poisson.PTX.Flow.eval
#print axioms PtxTorchLean.Poisson.PTX.Flow.tick
#print axioms PtxTorchLean.Poisson.PTX.Flow.execute
#print axioms PtxTorchLean.Poisson.PTX.Flow.eval_sound
#print axioms PtxTorchLean.Poisson.PTX.Flow.tick_sound
#print axioms PtxTorchLean.Poisson.PTX.Flow.execute_sound
#print axioms PtxTorchLean.Poisson.PTX.Flow.append
#print axioms PtxTorchLean.Poisson.PTX.Flow.halted_no_step
#print axioms PtxTorchLean.Poisson.PTX.Flow.invariant
#print axioms PtxTorchLean.Poisson.PTX.Flow.Counted
#print axioms PtxTorchLean.Poisson.PTX.Flow.counted
#print axioms PtxTorchLean.Poisson.PTX.Flow.counted_run
#print axioms PtxTorchLean.Poisson.PTX.Flow.peel
#print axioms PtxTorchLean.Poisson.PTX.Flow.peel_simple
#print axioms PtxTorchLean.Poisson.PTX.Flow.peel_block
#print axioms PtxTorchLean.Poisson.PTX.Flow.block_run
#print axioms PtxTorchLean.Poisson.PTX.Flow.Loop.header
#print axioms PtxTorchLean.Poisson.PTX.Flow.Loop.program
#print axioms PtxTorchLean.Poisson.PTX.Flow.Loop.exhausted
#print axioms PtxTorchLean.Poisson.PTX.Flow.Loop.Traversal
#print axioms PtxTorchLean.Poisson.PTX.Flow.Loop.halted_eq
#print axioms PtxTorchLean.Poisson.PTX.Flow.Loop.counted_traversal
#print axioms PtxTorchLean.Poisson.PTX.Flow.Loop.traversal
#print axioms PtxTorchLean.Poisson.PTX.Flow.Loop.traversal_runs
#print axioms PtxTorchLean.Poisson.PTX.Indexed.append
#print axioms PtxTorchLean.Poisson.PTX.Indexed.split
#print axioms PtxTorchLean.Poisson.PTX.Assembly.lookupCode
#print axioms PtxTorchLean.Poisson.PTX.Assembly.indexAddress
#print axioms PtxTorchLean.Poisson.PTX.Assembly.index
#print axioms PtxTorchLean.Poisson.PTX.Assembly.valueAddress
#print axioms PtxTorchLean.Poisson.PTX.Assembly.value
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Valid
#print axioms PtxTorchLean.Poisson.PTX.Assembly.loaded
#print axioms PtxTorchLean.Poisson.PTX.Assembly.lookup_execution
#print axioms PtxTorchLean.Poisson.PTX.Assembly.lookup_correct
#print axioms PtxTorchLean.Poisson.PTX.Assembly.body
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Stable
#print axioms PtxTorchLean.Poisson.PTX.Assembly.body_correct
#print axioms PtxTorchLean.Poisson.PTX.Assembly.body_exists
#print axioms PtxTorchLean.Poisson.PTX.Assembly.cursor
#print axioms PtxTorchLean.Poisson.PTX.Assembly.limit
#print axioms PtxTorchLean.Poisson.PTX.Assembly.atCursor
#print axioms PtxTorchLean.Poisson.PTX.Assembly.contribution
#print axioms PtxTorchLean.Poisson.PTX.Assembly.stable_refl
#print axioms PtxTorchLean.Poisson.PTX.Assembly.stable_trans
#print axioms PtxTorchLean.Poisson.PTX.Assembly.stable_limit
#print axioms PtxTorchLean.Poisson.PTX.Assembly.valid_at
#print axioms PtxTorchLean.Poisson.PTX.Assembly.value_at
#print axioms PtxTorchLean.Poisson.PTX.Assembly.cursor_increment
#print axioms PtxTorchLean.Poisson.PTX.Assembly.traversal_correct
#print axioms PtxTorchLean.Poisson.PTX.Assembly.fetched_correct
#print axioms PtxTorchLean.Poisson.PTX.Assembly.traversal_exists
#print axioms PtxTorchLean.Poisson.PTX.Assembly.fetched_exists
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Layout
#print axioms PtxTorchLean.Poisson.PTX.Assembly.valid_of_layout
#print axioms PtxTorchLean.Poisson.PTX.Assembly.layout_correct
#print axioms PtxTorchLean.Poisson.PTX.Assembly.layout_exists
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Checks.memory
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Checks.start
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Checks.ctx
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Checks.code
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Checks.candidate
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Checks.result
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Checks.executed
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Checks.actual
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Checks.cancellation
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Checks.layout
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Checks.fold_result
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Checks.fuel_rejected
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Checks.bad_index_rejected
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Checks.empty
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Text.register
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Text.operand
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Text.data
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Text.indexed
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Text.label
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Text.comparison
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Text.source
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Text.instruction
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Text.rendered

#print axioms PtxTorchLean.Poisson.PTX.Flow.Window.header
#print axioms PtxTorchLean.Poisson.PTX.Flow.Window.program
#print axioms PtxTorchLean.Poisson.PTX.Flow.Window.Traversal
#print axioms PtxTorchLean.Poisson.PTX.Flow.Window.cut
#print axioms PtxTorchLean.Poisson.PTX.Flow.Window.exit_pc
#print axioms PtxTorchLean.Poisson.PTX.Flow.noFP
#print axioms PtxTorchLean.Poisson.PTX.Flow.linear
#print axioms PtxTorchLean.Poisson.PTX.Flow.Sequence
#print axioms PtxTorchLean.Poisson.PTX.Flow.sequence
#print axioms PtxTorchLean.Poisson.PTX.Flow.sequence_sound
#print axioms PtxTorchLean.Poisson.PTX.Flow.eval_complete
#print axioms PtxTorchLean.Poisson.PTX.Flow.eval_unique
#print axioms PtxTorchLean.Poisson.PTX.Flow.linear_pc
#print axioms PtxTorchLean.Poisson.PTX.Flow.sequence_run
#print axioms PtxTorchLean.Poisson.PTX.Flow.consume_sequence
#print axioms PtxTorchLean.Poisson.PTX.Flow.sequence_append
#print axioms PtxTorchLean.Poisson.PTX.Flow.sequence_data
#print axioms PtxTorchLean.Poisson.PTX.Assembly.window_correct
#print axioms PtxTorchLean.Poisson.PTX.Assembly.prologue
#print axioms PtxTorchLean.Poisson.PTX.Assembly.setup
#print axioms PtxTorchLean.Poisson.PTX.Assembly.prologue_execution
#print axioms PtxTorchLean.Poisson.PTX.Assembly.setup_active
#print axioms PtxTorchLean.Poisson.PTX.Assembly.setup_inactive
#print axioms PtxTorchLean.Poisson.PTX.Assembly.prepareCode
#print axioms PtxTorchLean.Poisson.PTX.Assembly.offsetAddress
#print axioms PtxTorchLean.Poisson.PTX.Assembly.offsetValue
#print axioms PtxTorchLean.Poisson.PTX.Assembly.PrepareValid
#print axioms PtxTorchLean.Poisson.PTX.Assembly.prepared
#print axioms PtxTorchLean.Poisson.PTX.Assembly.prepare_execution
#print axioms PtxTorchLean.Poisson.PTX.Assembly.prepare_correct
#print axioms PtxTorchLean.Poisson.PTX.Assembly.entryPrefix
#print axioms PtxTorchLean.Poisson.PTX.Assembly.ready
#print axioms PtxTorchLean.Poisson.PTX.Assembly.prefix_trace
#print axioms PtxTorchLean.Poisson.PTX.Assembly.prefix_plain
#print axioms PtxTorchLean.Poisson.PTX.Assembly.prefix_linear
#print axioms PtxTorchLean.Poisson.PTX.Assembly.ready_pc
#print axioms PtxTorchLean.Poisson.PTX.Assembly.ready_running
#print axioms PtxTorchLean.Poisson.PTX.Assembly.maskLoad
#print axioms PtxTorchLean.Poisson.PTX.Assembly.maskAddress
#print axioms PtxTorchLean.Poisson.PTX.Assembly.maskFlag
#print axioms PtxTorchLean.Poisson.PTX.Assembly.maskLoaded
#print axioms PtxTorchLean.Poisson.PTX.Assembly.mask_load_execution
#print axioms PtxTorchLean.Poisson.PTX.Assembly.maskCode
#print axioms PtxTorchLean.Poisson.PTX.Assembly.masked
#print axioms PtxTorchLean.Poisson.PTX.Assembly.mask_trace
#print axioms PtxTorchLean.Poisson.PTX.Assembly.maskedWord
#print axioms PtxTorchLean.Poisson.PTX.Assembly.masked_value
#print axioms PtxTorchLean.Poisson.PTX.Assembly.masked_frame
#print axioms PtxTorchLean.Poisson.PTX.Indexed.keeps
#print axioms PtxTorchLean.Poisson.PTX.Indexed.eval_keeps
#print axioms PtxTorchLean.Poisson.PTX.Indexed.block_keeps
#print axioms PtxTorchLean.Poisson.PTX.Indexed.scalar_block
#print axioms PtxTorchLean.Poisson.PTX.Assembly.outputCode
#print axioms PtxTorchLean.Poisson.PTX.Assembly.outputFinish
#print axioms PtxTorchLean.Poisson.PTX.Assembly.output_trace
#print axioms PtxTorchLean.Poisson.PTX.Assembly.tailCode
#print axioms PtxTorchLean.Poisson.PTX.Assembly.tailStart
#print axioms PtxTorchLean.Poisson.PTX.Assembly.tailFinish
#print axioms PtxTorchLean.Poisson.PTX.Assembly.mask_address
#print axioms PtxTorchLean.Poisson.PTX.Assembly.tail_trace
#print axioms PtxTorchLean.Poisson.PTX.Assembly.finalWord
#print axioms PtxTorchLean.Poisson.PTX.Assembly.tail_memory
#print axioms PtxTorchLean.Poisson.PTX.Assembly.tail_returned
#print axioms PtxTorchLean.Poisson.PTX.Assembly.tail_plain
#print axioms PtxTorchLean.Poisson.PTX.Assembly.tail_linear
#print axioms PtxTorchLean.Poisson.PTX.Assembly.entryCode
#print axioms PtxTorchLean.Poisson.PTX.Assembly.beforeOutput
#print axioms PtxTorchLean.Poisson.PTX.Assembly.window_node
#print axioms PtxTorchLean.Poisson.PTX.Assembly.entry_loop
#print axioms PtxTorchLean.Poisson.PTX.Assembly.entry_tail
#print axioms PtxTorchLean.Poisson.PTX.Assembly.entryValue
#print axioms PtxTorchLean.Poisson.PTX.Assembly.ready_zero
#print axioms PtxTorchLean.Poisson.PTX.Assembly.entry_written
#print axioms PtxTorchLean.Poisson.PTX.Flow.Window.traversal_runs
#print axioms PtxTorchLean.Poisson.PTX.Assembly.window_exists
#print axioms PtxTorchLean.Poisson.PTX.Assembly.inactive_result
#print axioms PtxTorchLean.Poisson.PTX.Assembly.entry_exists
#print axioms PtxTorchLean.Poisson.PTX.Assembly.EntryChecks.memory
#print axioms PtxTorchLean.Poisson.PTX.Assembly.EntryChecks.start
#print axioms PtxTorchLean.Poisson.PTX.Assembly.EntryChecks.ctx
#print axioms PtxTorchLean.Poisson.PTX.Assembly.EntryChecks.code
#print axioms PtxTorchLean.Poisson.PTX.Assembly.EntryChecks.candidate
#print axioms PtxTorchLean.Poisson.PTX.Assembly.EntryChecks.result
#print axioms PtxTorchLean.Poisson.PTX.Assembly.EntryChecks.executed
#print axioms PtxTorchLean.Poisson.PTX.Assembly.EntryChecks.actual
#print axioms PtxTorchLean.Poisson.PTX.Assembly.EntryChecks.stored
#print axioms PtxTorchLean.Poisson.PTX.Assembly.EntryChecks.layout
#print axioms PtxTorchLean.Poisson.PTX.Assembly.EntryChecks.full_result
#print axioms PtxTorchLean.Poisson.PTX.Assembly.EntryChecks.exists_for_inputs
#print axioms PtxTorchLean.Poisson.PTX.Assembly.EntryChecks.padding
#print axioms PtxTorchLean.Poisson.PTX.Assembly.EntryChecks.bad_offset_rejected
#print axioms PtxTorchLean.Poisson.PTX.Assembly.EntryChecks.bad_output_rejected
#print axioms PtxTorchLean.Poisson.PTX.Assembly.EntryChecks.bad_index_rejected
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Text.fullInstruction
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Text.fullRendered
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Text.fullShape
#print axioms PtxTorchLean.Poisson.PTX.Assembly.inactive_exists

#print axioms PtxTorchLean.Poisson.PTX.Assembly.Arena
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Arena.context
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Arena.start
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Arena.offset
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Arena.Contents
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Arena.index
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Arena.live
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Arena.offset_index
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Arena.offset_address
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Arena.prepare_valid
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Arena.ready_cursor
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Arena.ready_limit
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Arena.output_address
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Arena.boundary_address
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Arena.output_valid
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Arena.boundary_valid
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Arena.loop_layout
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Arena.complete
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Arena.exists
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Arena.owners
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Arena.entryIndex
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Arena.elementValue
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Arena.row
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Arena.value
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Arena.contribution_value
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Arena.value_eq
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Rows.selected
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Rows.contributions
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Rows.ordered
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Rows.interleaved
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Snapshot.Finished
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Snapshot.address
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Snapshot.word
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Snapshot.written
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Snapshot.publish
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Snapshot.published_word
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Snapshot.published_value
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Snapshot.published_outside
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Snapshot.witness
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Snapshot.scatter
#print axioms PtxTorchLean.Poisson.PTX.Assembly.ArenaChecks.arena
#print axioms PtxTorchLean.Poisson.PTX.Assembly.ArenaChecks.memory
#print axioms PtxTorchLean.Poisson.PTX.Assembly.ArenaChecks.contents
#print axioms PtxTorchLean.Poisson.PTX.Assembly.ArenaChecks.candidate
#print axioms PtxTorchLean.Poisson.PTX.Assembly.ArenaChecks.result
#print axioms PtxTorchLean.Poisson.PTX.Assembly.ArenaChecks.executed
#print axioms PtxTorchLean.Poisson.PTX.Assembly.ArenaChecks.finished
#print axioms PtxTorchLean.Poisson.PTX.Assembly.ArenaChecks.row_order
#print axioms PtxTorchLean.Poisson.PTX.Assembly.ArenaChecks.values
#print axioms PtxTorchLean.Poisson.PTX.Assembly.ArenaChecks.published
#print axioms PtxTorchLean.Poisson.PTX.Assembly.ArenaChecks.scatter
#print axioms PtxTorchLean.Poisson.PTX.Flow.Observed.Eval
#print axioms PtxTorchLean.Poisson.PTX.Flow.Observed.Step
#print axioms PtxTorchLean.Poisson.PTX.Flow.Observed.Runs
#print axioms PtxTorchLean.Poisson.PTX.Flow.Observed.replay_step
#print axioms PtxTorchLean.Poisson.PTX.Flow.Observed.append
#print axioms PtxTorchLean.Poisson.PTX.Flow.Observed.store_shape
#print axioms PtxTorchLean.Poisson.PTX.Flow.Observed.ReadFrame
#print axioms PtxTorchLean.Poisson.PTX.Flow.Observed.Separate
#print axioms PtxTorchLean.Poisson.PTX.Flow.Observed.put_frame
#print axioms PtxTorchLean.Poisson.PTX.Flow.Observed.data_frame
#print axioms PtxTorchLean.Poisson.PTX.Flow.Observed.simple_frame
#print axioms PtxTorchLean.Poisson.PTX.Flow.Observed.step_frame
#print axioms PtxTorchLean.Poisson.PTX.Flow.Observed.replay
#print axioms PtxTorchLean.Poisson.PTX.Flow.Observed.events
#print axioms PtxTorchLean.Poisson.PTX.Flow.Observed.indexEvents
#print axioms PtxTorchLean.Poisson.PTX.Flow.Observed.source_values
#print axioms PtxTorchLean.Poisson.PTX.Flow.Observed.admitted_replay
#print axioms PtxTorchLean.Poisson.PTX.Flow.Observed.data_exists
#print axioms PtxTorchLean.Poisson.PTX.Flow.Observed.eval_exists
#print axioms PtxTorchLean.Poisson.PTX.Flow.Observed.run_exists
#print axioms PtxTorchLean.Poisson.PTX.Flow.Parallel.Runs
#print axioms PtxTorchLean.Poisson.PTX.Flow.Parallel.wordsFor
#print axioms PtxTorchLean.Poisson.PTX.Flow.Parallel.indicesFor
#print axioms PtxTorchLean.Poisson.PTX.Flow.Parallel.project
#print axioms PtxTorchLean.Poisson.PTX.Flow.Parallel.word_member
#print axioms PtxTorchLean.Poisson.PTX.Flow.Parallel.index_member
#print axioms PtxTorchLean.Poisson.PTX.Flow.Parallel.Separate
#print axioms PtxTorchLean.Poisson.PTX.Flow.Parallel.values
#print axioms PtxTorchLean.Poisson.PTX.Flow.Parallel.replay
#print axioms PtxTorchLean.Poisson.PTX.Flow.Observed.Checks.memory
#print axioms PtxTorchLean.Poisson.PTX.Flow.Observed.Checks.start
#print axioms PtxTorchLean.Poisson.PTX.Flow.Observed.Checks.ctx
#print axioms PtxTorchLean.Poisson.PTX.Flow.Observed.Checks.code
#print axioms PtxTorchLean.Poisson.PTX.Flow.Observed.Checks.indexed
#print axioms PtxTorchLean.Poisson.PTX.Flow.Observed.Checks.loaded
#print axioms PtxTorchLean.Poisson.PTX.Flow.Observed.Checks.stored
#print axioms PtxTorchLean.Poisson.PTX.Flow.Observed.Checks.final
#print axioms PtxTorchLean.Poisson.PTX.Flow.Observed.Checks.words
#print axioms PtxTorchLean.Poisson.PTX.Flow.Observed.Checks.indices
#print axioms PtxTorchLean.Poisson.PTX.Flow.Observed.Checks.actual
#print axioms PtxTorchLean.Poisson.PTX.Flow.Observed.Checks.compatible
#print axioms PtxTorchLean.Poisson.PTX.Flow.Observed.Checks.index_compatible
#print axioms PtxTorchLean.Poisson.PTX.Flow.Observed.Checks.separated
#print axioms PtxTorchLean.Poisson.PTX.Flow.Observed.Checks.replayed
#print axioms PtxTorchLean.Poisson.PTX.Flow.Observed.Checks.output
#print axioms PtxTorchLean.Poisson.PTX.Flow.Observed.Checks.forged_rejected
#print axioms PtxTorchLean.Poisson.PTX.Assembly.ObservedAddress.Ready
#print axioms PtxTorchLean.Poisson.PTX.Assembly.ObservedAddress.initial
#print axioms PtxTorchLean.Poisson.PTX.Assembly.ObservedAddress.step_ready
#print axioms PtxTorchLean.Poisson.PTX.Assembly.ObservedAddress.store_address
#print axioms PtxTorchLean.Poisson.PTX.Assembly.ObservedAddress.stores
#print axioms PtxTorchLean.Poisson.PTX.Assembly.parallel_stores
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Arena.parallel_store
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Arena.parallel_owners

#print axioms PtxTorchLean.Poisson.PTX.Assembly.ObservedAddress.BeforeStore
#print axioms PtxTorchLean.Poisson.PTX.Assembly.ObservedAddress.before_store_step
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Arena.FieldApart
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Arena.InputSeparation
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Arena.index_initial
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Arena.word_initial
#print axioms PtxTorchLean.Poisson.PTX.Assembly.ObservedAddress.BoundsReady
#print axioms PtxTorchLean.Poisson.PTX.Assembly.ObservedAddress.bounds_initial
#print axioms PtxTorchLean.Poisson.PTX.Assembly.ObservedAddress.bounds_step
#print axioms PtxTorchLean.Poisson.PTX.Assembly.ObservedAddress.IndexReady
#print axioms PtxTorchLean.Poisson.PTX.Assembly.ObservedAddress.index_initial
#print axioms PtxTorchLean.Poisson.PTX.Assembly.ObservedAddress.index_step
#print axioms PtxTorchLean.Poisson.PTX.Assembly.ObservedAddress.nodeWord
#print axioms PtxTorchLean.Poisson.PTX.Assembly.ObservedAddress.nextWord
#print axioms PtxTorchLean.Poisson.PTX.Assembly.ObservedAddress.nodeScale
#print axioms PtxTorchLean.Poisson.PTX.Assembly.ObservedAddress.nextScale
#print axioms PtxTorchLean.Poisson.PTX.Assembly.ObservedAddress.OffsetsReady
#print axioms PtxTorchLean.Poisson.PTX.Assembly.ObservedAddress.offsets_initial
#print axioms PtxTorchLean.Poisson.PTX.Assembly.ObservedAddress.offsets_step
#print axioms PtxTorchLean.Poisson.PTX.Assembly.ObservedAddress.scaled4
#print axioms PtxTorchLean.Poisson.PTX.Assembly.ObservedAddress.scaled8
#print axioms PtxTorchLean.Poisson.PTX.Assembly.ObservedAddress.ReadAddressReady
#print axioms PtxTorchLean.Poisson.PTX.Assembly.ObservedAddress.read_address_initial
#print axioms PtxTorchLean.Poisson.PTX.Assembly.ObservedAddress.read_address_step
#print axioms PtxTorchLean.Poisson.PTX.Assembly.ObservedAddress.offset_address
#print axioms PtxTorchLean.Poisson.PTX.Assembly.ObservedAddress.offset_records
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Arena.offset_record
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Arena.offset_source
#print axioms PtxTorchLean.Poisson.PTX.Assembly.ParallelChecks.separated
#print axioms PtxTorchLean.Poisson.PTX.Assembly.ParallelChecks.nonzero_admitted
#print axioms PtxTorchLean.Poisson.PTX.Assembly.ParallelChecks.separation_cases
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Arena.parallel_publication
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Arena.parallel_value
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Arena.parallel_scatter
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Arena.parallel_exists
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Arena.parallel_exists_correct
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Arena.parallel_separate
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Arena.parallel_replay
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Arena.finished
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Arena.loop_index_field
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Arena.boundary_field
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Arena.element_field
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Arena.InputRead
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Arena.read_footprints
#print axioms PtxTorchLean.Poisson.PTX.Assembly.ObservedAddress.index_site
#print axioms PtxTorchLean.Poisson.PTX.Assembly.ObservedAddress.word_site
#print axioms PtxTorchLean.Poisson.PTX.Assembly.recorded_witness
#print axioms PtxTorchLean.Poisson.PTX.Flow.Observed.index_shape
#print axioms PtxTorchLean.Poisson.PTX.Flow.Observed.load_shape
#print axioms PtxTorchLean.Poisson.PTX.Flow.Parallel.append
#print axioms PtxTorchLean.Poisson.PTX.Flow.Parallel.lift
#print axioms PtxTorchLean.Poisson.PTX.Flow.Parallel.combine
#print axioms PtxTorchLean.Poisson.PTX.Flow.Parallel.all_threads
#print axioms PtxTorchLean.Poisson.PTX.Flow.Parallel.publication_byte
#print axioms PtxTorchLean.Poisson.PTX.Flow.Parallel.publication_word
#print axioms PtxTorchLean.Poisson.PTX.Flow.Observed.applyAccess
#print axioms PtxTorchLean.Poisson.PTX.Flow.Observed.data_memory
#print axioms PtxTorchLean.Poisson.PTX.Flow.Observed.simple_memory
#print axioms PtxTorchLean.Poisson.PTX.Flow.Observed.step_memory
#print axioms PtxTorchLean.Poisson.PTX.Flow.Observed.applyAccess_congr
#print axioms PtxTorchLean.Poisson.PTX.Flow.Observed.applyAccess_outside
#print axioms PtxTorchLean.Poisson.PTX.Flow.Observed.applyEvent_eq
#print axioms PtxTorchLean.Poisson.PTX.Flow.Observed.data_read_witness
#print axioms PtxTorchLean.Poisson.PTX.Flow.Observed.step_read_witness
#print axioms PtxTorchLean.Poisson.PTX.Flow.Observed.walk

#print axioms PtxTorchLean.Poisson.PTX.Assembly.CompressedRows.offset
#print axioms PtxTorchLean.Poisson.PTX.Assembly.CompressedRows.offset_le_length
#print axioms PtxTorchLean.Poisson.PTX.Assembly.CompressedRows.offset_next
#print axioms PtxTorchLean.Poisson.PTX.Assembly.CompressedRows.entry
#print axioms PtxTorchLean.Poisson.PTX.Assembly.CompressedRows.range_inside
#print axioms PtxTorchLean.Poisson.PTX.Assembly.CompressedRows.reconstruct
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Arena.RowsEncoded
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Arena.RowsEncoded.contents
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Arena.RowsEncoded.row
#print axioms PtxTorchLean.Poisson.PTX.Assembly.nodeRows
#print axioms PtxTorchLean.Poisson.PTX.Assembly.nodeRows_get
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Arena.RowsEncoded.selected
#print axioms PtxTorchLean.Poisson.PTX.Assembly.MeshRows.locations
#print axioms PtxTorchLean.Poisson.PTX.Assembly.MeshRows.scatter_indices
#print axioms PtxTorchLean.Poisson.PTX.Assembly.MeshRows.contributions_eq
#print axioms PtxTorchLean.Poisson.PTX.Assembly.MeshRows.operator_sum
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Rows.insert
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Rows.scan
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Rows.scan_from
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Rows.scan_selected
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Rows.selected_bound
#print axioms PtxTorchLean.Poisson.PTX.Assembly.nodeRows_bound
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Arena.parallel_operator
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Arena.parallel_masked_operator
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Arena.checkRows
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Arena.checkRows_sound
#print axioms PtxTorchLean.Poisson.PTX.Assembly.Arena.checkRows_complete
#print axioms PtxTorchLean.Poisson.PTX.Assembly.TableChecks.input_checked
#print axioms PtxTorchLean.Poisson.PTX.Assembly.TableChecks.input_represented
#print axioms PtxTorchLean.Poisson.PTX.Assembly.TableChecks.wrong_order_rejected
#print axioms PtxTorchLean.Poisson.PTX.Assembly.TableChecks.corrupt_offset_rejected
#print axioms PtxTorchLean.Poisson.PTX.Assembly.TableChecks.corrupt_index_rejected
#print axioms PtxTorchLean.Poisson.PTX.Assembly.TableChecks.empty_rows
#print axioms PtxTorchLean.Poisson.PTX.Assembly.TableChecks.host_scan
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.Execution
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.Execution.tensor
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Padding.allowed
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Padding.Boundaries
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Padding.boundaries
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Padding.initial
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Padding.Invariant
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Padding.step_invariant
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Padding.runs_invariant
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Padding.access_active
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.Execution.global_store
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.Execution.outside
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.Family
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.Family.address
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.Family.cell_nat
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.Family.entry
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.different_plane
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.Family.other_preserves
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.Family.publish
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.Family.published_entry
#print axioms PtxTorchLean.Poisson.PTX.OperatorMesh
#print axioms PtxTorchLean.Poisson.PTX.OperatorMesh.connectivity
#print axioms PtxTorchLean.Poisson.PTX.OperatorMesh.input
#print axioms PtxTorchLean.Poisson.PTX.OperatorMesh.gather
#print axioms PtxTorchLean.Poisson.PTX.OperatorMesh.operator
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.Family.before
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.Family.input_word32
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.Family.assembly_tables
#print axioms PtxTorchLean.Poisson.PTX.cell_assembly_operator
#print axioms PtxTorchLean.Poisson.PTX.cell_assembly_exists
#print axioms PtxTorchLean.Poisson.PTX.CellAssemblyWitness.one
#print axioms PtxTorchLean.Poisson.PTX.CellAssemblyWitness.memory
#print axioms PtxTorchLean.Poisson.PTX.CellAssemblyWitness.operator
#print axioms PtxTorchLean.Poisson.PTX.CellAssemblyWitness.values
#print axioms PtxTorchLean.Poisson.PTX.CellAssemblyWitness.seed
#print axioms PtxTorchLean.Poisson.PTX.CellAssemblyWitness.start
#print axioms PtxTorchLean.Poisson.PTX.CellAssemblyWitness.cfg
#print axioms PtxTorchLean.Poisson.PTX.CellAssemblyWitness.bases
#print axioms PtxTorchLean.Poisson.PTX.CellAssemblyWitness.context
#print axioms PtxTorchLean.Poisson.PTX.CellAssemblyWitness.prefixChoice
#print axioms PtxTorchLean.Poisson.PTX.CellAssemblyWitness.prefixCandidate
#print axioms PtxTorchLean.Poisson.PTX.CellAssemblyWitness.prefixResult
#print axioms PtxTorchLean.Poisson.PTX.CellAssemblyWitness.prefix_executed
#print axioms PtxTorchLean.Poisson.PTX.CellAssemblyWitness.addressSeed
#print axioms PtxTorchLean.Poisson.PTX.CellAssemblyWitness.addressStep
#print axioms PtxTorchLean.Poisson.PTX.CellAssemblyWitness.addressState
#print axioms PtxTorchLean.Poisson.PTX.CellAssemblyWitness.bodyChoice
#print axioms PtxTorchLean.Poisson.PTX.CellAssemblyWitness.bodyStart
#print axioms PtxTorchLean.Poisson.PTX.CellAssemblyWitness.bodyCandidate
#print axioms PtxTorchLean.Poisson.PTX.CellAssemblyWitness.bodyResult
#print axioms PtxTorchLean.Poisson.PTX.CellAssemblyWitness.body_executed
#print axioms PtxTorchLean.Poisson.PTX.CellAssemblyWitness.events
#print axioms PtxTorchLean.Poisson.PTX.CellAssemblyWitness.final
#print axioms PtxTorchLean.Poisson.PTX.CellAssemblyWitness.actual
#print axioms PtxTorchLean.Poisson.PTX.CellAssemblyWitness.returned
#print axioms PtxTorchLean.Poisson.PTX.CellAssemblyWitness.initial
#print axioms PtxTorchLean.Poisson.PTX.CellAssemblyWitness.admitted
#print axioms PtxTorchLean.Poisson.PTX.CellAssemblyWitness.aligned
#print axioms PtxTorchLean.Poisson.PTX.CellAssemblyWitness.performed
#print axioms PtxTorchLean.Poisson.PTX.CellAssemblyWitness.indices_admitted
#print axioms PtxTorchLean.Poisson.PTX.CellAssemblyWitness.layout
#print axioms PtxTorchLean.Poisson.PTX.CellAssemblyWitness.coefficients
#print axioms PtxTorchLean.Poisson.PTX.CellAssemblyWitness.execution
#print axioms PtxTorchLean.Poisson.PTX.CellAssemblyWitness.family
#print axioms PtxTorchLean.Poisson.PTX.CellAssemblyWitness.meshShape
#print axioms PtxTorchLean.Poisson.PTX.CellAssemblyWitness.arena
#print axioms PtxTorchLean.Poisson.PTX.CellAssemblyWitness.tables_checked
#print axioms PtxTorchLean.Poisson.PTX.CellAssemblyWitness.separated
#print axioms PtxTorchLean.Poisson.PTX.CellAssemblyWitness.numerical
#print axioms PtxTorchLean.Poisson.PTX.CellAssemblyWitness.composed

#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Padding.checkBoundaries
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Padding.checkBoundaries_sound

#print axioms PtxTorchLean.Poisson.PTX.Concurrent.WordSourceCheck.expected
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.WordSourceCheck.check
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.WordSourceCheck.sound

#print axioms PtxTorchLean.Poisson.PTX.CellAssemblyWitness.forged_word_rejected

#print axioms PtxTorchLean.Poisson.PTX.ArrayOperator.scatter
#print axioms PtxTorchLean.Poisson.PTX.ArrayOperator.flat
#print axioms PtxTorchLean.Poisson.PTX.ArrayOperator.localValues
#print axioms PtxTorchLean.Poisson.PTX.ArrayOperator.result
#print axioms PtxTorchLean.Poisson.PTX.ArrayOperator.apply_valid
#print axioms PtxTorchLean.Poisson.PTX.ArrayOperator.addAt
#print axioms PtxTorchLean.Poisson.PTX.ArrayOperator.contributions
#print axioms PtxTorchLean.Poisson.PTX.ArrayOperator.scatter_fold
#print axioms PtxTorchLean.Poisson.PTX.ArrayOperator.addAt_size
#print axioms PtxTorchLean.Poisson.PTX.ArrayOperator.addAt_get
#print axioms PtxTorchLean.Poisson.PTX.ArrayOperator.fold_size
#print axioms PtxTorchLean.Poisson.PTX.ArrayOperator.fold_get
#print axioms PtxTorchLean.Poisson.PTX.ArrayOperator.range_product
#print axioms PtxTorchLean.Poisson.PTX.ArrayOperator.finRange_values
#print axioms PtxTorchLean.Poisson.PTX.ArrayOperator.localValues_entry
#print axioms PtxTorchLean.Poisson.PTX.ArrayOperator.contributions_tensor
#print axioms PtxTorchLean.Poisson.PTX.ArrayOperator.result_size
#print axioms PtxTorchLean.Poisson.PTX.ArrayOperator.result_get
#print axioms PtxTorchLean.Poisson.PTX.ArrayOperator.result_tensor
#print axioms PtxTorchLean.Poisson.PTX.ArrayOperator.apply_correspondence
#print axioms PtxTorchLean.Poisson.PTX.cell_assembly_reference
#print axioms PtxTorchLean.Poisson.PTX.ArrayOperator.Checks.reference_nonzero
#print axioms PtxTorchLean.Poisson.PTX.ArrayOperator.Checks.wrong_length
#print axioms PtxTorchLean.Poisson.PTX.ArrayOperator.Checks.nonfinite
#print axioms PtxTorchLean.Poisson.PTX.ArrayOperator.Checks.cancellation_order

#print axioms PtxTorchLean.Poisson.PTX.CellGrid.Launch
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.config
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.Runs
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.forBlock
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.forBlock_append
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.forBlock_tag
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.project
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.ByteAddress
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.byteAddress
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.global_common
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.shared_private
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.initial
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.Compatible
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.localSource
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.NoForeignOverlap
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.shared_source_owner
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.source_owner
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.compatible_project
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.Performed
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.performed_project
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.publish
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.applyEvent_congr
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.publication_byte
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.publication_word
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.mem_forBlock
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.cell_words_disjoint
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.family_entry
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.family_before
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.Candidate
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.Candidate.withSources
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.Candidate.global_store
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.Candidate.inputLayout
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.Candidate.past
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.Candidate.index_bound
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.Candidate.word_bound
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.IndexCompatible
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.index_initial
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.Candidates
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.Candidates.store_lower
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.Candidates.index_values
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.Candidates.separated
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.Candidates.withSources
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.Execution
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.Admitted
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.Admitted.family
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.Admitted.entry
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.Admitted.before
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.Admitted.input_word32
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.Admitted.assembly_tables
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.assembly_operator
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.assembly_exists
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.assembly_reference
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.Checks.sharedEvents
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.Checks.foreign
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.Checks.foreign_shared_rejected
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.Checks.identities
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.Checks.stores
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.Checks.interleaved_publication
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.Checks.seed
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.Checks.start
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.Checks.launch
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.Checks.after
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.Checks.first_step
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.Checks.two_blocks
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.Checks.projected_step

#print axioms PtxTorchLean.Poisson.PTX.CellGrid.append
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.lift_block
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.prefixState
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.prefix_update
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.prefix_exists
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.serial_exists
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.liftSource
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.compatible_lift
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.index_compatible_lift
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.performed_lift
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.Execution.candidate
#print axioms PtxTorchLean.Poisson.PTX.CellWhole.Family.candidates
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.familyLaunch
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.family_config
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.family_exists
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.ExistsChecks.nonzero_grid
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.ExistsChecks.nonzero_assembly

#print axioms PtxTorchLean.Poisson.PTX.Assembly.Arena.parallel_preserves_word
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.ResidualLayout
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.Admitted.input_word64
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.ResidualLayout.rhs_preserved
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.residual_correspondence
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.ResidualChecks.residualArena
#print axioms PtxTorchLean.Poisson.PTX.CellGrid.ResidualChecks.fresh_minus_seven

#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Visibility.Repeated.ThreadBefore
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Visibility.Repeated.Edge
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Visibility.Repeated.Before
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Visibility.Repeated.before_lt
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Visibility.Repeated.OrderedSources
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Visibility.Repeated.OrderedSources.performed
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Visibility.Repeated.WritersAround
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Visibility.Repeated.read_from_stage
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Visibility.Repeated.Checks.program
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Visibility.Repeated.Checks.start
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Visibility.Repeated.Checks.cfg
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Visibility.Repeated.Checks.execution
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Visibility.Repeated.Checks.result
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Visibility.Repeated.Checks.history
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Visibility.Repeated.Checks.source
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Visibility.Repeated.Checks.executed
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Visibility.Repeated.Checks.actual
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Visibility.Repeated.Checks.read_index
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Visibility.Repeated.Checks.store_index
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Visibility.Repeated.Checks.old_constraints
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Visibility.Repeated.Checks.obsolete_passes_old
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Visibility.Repeated.Checks.future_passes_old
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Visibility.Repeated.Checks.newest_compatible
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Visibility.Repeated.Checks.thread_before
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Visibility.Repeated.Checks.future_rejected
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Visibility.Repeated.Checks.obsolete_rejected
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Visibility.Repeated.Checks.newest_admissible
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Visibility.Repeated.Checks.forced_stage
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Visibility.Repeated.OrderChecks.separate
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Visibility.Repeated.OrderChecks.no_edge
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Visibility.Repeated.OrderChecks.chronological_is_not_causal
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Visibility.Repeated.OrderChecks.program
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Visibility.Repeated.OrderChecks.start
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Visibility.Repeated.OrderChecks.cfg
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Visibility.Repeated.OrderChecks.execution
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Visibility.Repeated.OrderChecks.result
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Visibility.Repeated.OrderChecks.history
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Visibility.Repeated.OrderChecks.executed
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Visibility.Repeated.OrderChecks.actual
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Visibility.Repeated.OrderChecks.synchronized

#print axioms PtxTorchLean.Poisson.PTX.Reduction.Update.code
#print axioms PtxTorchLean.Poisson.PTX.Reduction.Update.address
#print axioms PtxTorchLean.Poisson.PTX.Reduction.Update.left
#print axioms PtxTorchLean.Poisson.PTX.Reduction.Update.right
#print axioms PtxTorchLean.Poisson.PTX.Reduction.Update.loaded
#print axioms PtxTorchLean.Poisson.PTX.Reduction.Update.finish
#print axioms PtxTorchLean.Poisson.PTX.Reduction.Update.Valid
#print axioms PtxTorchLean.Poisson.PTX.Reduction.Update.effect
#print axioms PtxTorchLean.Poisson.PTX.Reduction.Update.run_update
#print axioms PtxTorchLean.Poisson.PTX.Reduction.Update.exists_execution
#print axioms PtxTorchLean.Poisson.PTX.Reduction.Update.correct
#print axioms PtxTorchLean.Poisson.PTX.Reduction.Update.preserves_other_bytes
#print axioms PtxTorchLean.Poisson.PTX.Reduction.Update.fetched_correct
#print axioms PtxTorchLean.Poisson.PTX.Reduction.Update.fetched_exists
#print axioms PtxTorchLean.Poisson.PTX.Reduction.Update.valid_of_active
#print axioms PtxTorchLean.Poisson.PTX.Reduction.Update.Checks.state
#print axioms PtxTorchLean.Poisson.PTX.Reduction.Update.Checks.boundary_sum
#print axioms PtxTorchLean.Poisson.PTX.Reduction.Update.Checks.neighbor_unchanged
#print axioms PtxTorchLean.Poisson.PTX.Reduction.Update.Checks.past_end_rejected
#print axioms PtxTorchLean.Poisson.PTX.Reduction.Update.Checks.misaligned_rejected
#print axioms PtxTorchLean.Poisson.PTX.Reduction.Update.Checks.rounding
#print axioms PtxTorchLean.Poisson.PTX.Reduction.Update.Checks.rounded_addition
#print axioms PtxTorchLean.Poisson.PTX.Reduction.Update.Checks.instruction_text

#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.LaneStores
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.owner_of_overlap
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.before_of_pc
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.own_writers_around
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.neighbor_writers_around
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.own_read
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.neighbor_read
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.active
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.active_antitone
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.StageStores
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.own_gap
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.neighbor_last
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.stage_own_read
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.stage_neighbor_read
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Witness.program
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Witness.input
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Witness.start
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Witness.cfg
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Witness.choose
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Witness.schedule
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Witness.execution
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Witness.result
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Witness.sum
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Witness.fence
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Witness.history
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Witness.recorded
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Witness.executed
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Witness.actual
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Witness.completed
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Witness.forward
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Witness.lane_stores
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Witness.own_gap
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Witness.neighbor_last
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Witness.neighbor_across
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Witness.forced_final_inputs
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Witness.forced_final_store
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Witness.final_store
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Witness.read_index
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Witness.store_index
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Witness.sourceIndex
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Witness.sources
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Witness.compatible
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Witness.ordered
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Witness.admitted_result
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Witness.stale_neighbor_rejected

#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Witness.stale_sources
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Witness.stale_compatible
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Witness.stale_candidate

#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Limits.Invariant
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Limits.Boundaries
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Limits.step_invariant
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Limits.runs_invariant
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Limits.access_active
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.AddressHold.keep
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.AddressHold.keep_correct
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.AddressHold.nextTag
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.AddressHold.tag
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.AddressHold.tag_zero
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.AddressHold.tag_next
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.AddressHold.ready_kept
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.AddressHold.data_ready
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.AddressHold.Entries
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.AddressHold.Invariant
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.AddressHold.step_invariant
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.AddressHold.runs_invariant
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.site
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.stage
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.program
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.limit
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.length
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.sites
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.checked_boundaries
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.boundaries
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.checked_stores
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.checked_forward
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.forward
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.store_coverage
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.checked_frames
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.frames
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.checked_entries
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.entries
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.checked_addresses
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.lane_stores
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.stage_stores
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.storeAddress
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.store_fetch
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.barrier_fetch
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.checked_writer_paths
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.writer_stops
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.checked_barrier_paths
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.barrier_stops
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.published
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.previous
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.current
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.readPC
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.readOffset
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.readAddress
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.checked_reads
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.ranges
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.read_geometry
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.checked_read_sites
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.read_coverage
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.selected_read
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.every_read
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Checks.extra_writers_rejected
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Checks.skipped_barrier_rejected
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Checks.clobbered_address_rejected

#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Values.empty
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Values.operand
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Values.transfer
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Values.Ready
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Values.empty_ready
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Values.operand_ready
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Values.assign_ready
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Values.data_ready
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Values.tag
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Values.Entries
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Values.Reads
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Values.Invariant
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Values.step_invariant
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Values.runs_invariant
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Numeric.values
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Numeric.final_value
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Numeric.initial
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Numeric.loads
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Numeric.initial_tag
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Numeric.update_tag
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Numeric.checked_targets
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Numeric.entries
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Numeric.stored
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Numeric.publication_limits
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Numeric.publication_value
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Numeric.completed_result
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Local.Block
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Local.pc
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Local.lift
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Serial.partialState
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Serial.prefix_zero
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Serial.prefix_all
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Serial.prefix_next
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Serial.run_lanes
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Witness256.sum
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Witness256.prepared
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Witness256.loaded
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Witness256.finish
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Witness256.updateEvents
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Witness256.update_block
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Witness256.initialEvents
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Witness256.initial_block
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Witness256.words
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Witness256.Expected
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Witness256.initial_expected
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Witness256.update_expected
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Witness256.Frame
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Witness256.frame_advance
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Witness256.frame_initial
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Witness256.frame_update
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Witness256.initial_valid
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Witness256.update_valid
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Witness256.initial_pc
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Witness256.update_pc
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Witness256.initial_fetch
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Witness256.update_fetch
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Witness256.guard_fetch
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Witness256.barrier_events
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Witness256.ReadyAt
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Witness256.round_expected
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Witness256.initial_wave
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Witness256.stageTarget
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Witness256.stage_wave
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Visibility.Repeated.Producer
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Visibility.Repeated.construct_sources
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Witness256.admitted
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Witness256.candidate_exists
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Witness256.exists_correct
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Witness256.Checks.cfg
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Witness256.Checks.start
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Witness256.Checks.ready
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Witness256.Checks.arbitrary_words
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Witness256.Checks.cancellation_result
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.checked_memory_spaces
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.access_shared
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.memory_safety

#print axioms PtxTorchLean.Poisson.PTX.Flow.Boundary.peel
#print axioms PtxTorchLean.Poisson.PTX.Flow.Boundary.peel_simple
#print axioms PtxTorchLean.Poisson.PTX.Flow.Boundary.peel_block
#print axioms PtxTorchLean.Poisson.PTX.Flow.OperandWindow.header
#print axioms PtxTorchLean.Poisson.PTX.Flow.OperandWindow.program
#print axioms PtxTorchLean.Poisson.PTX.Flow.OperandWindow.exhausted
#print axioms PtxTorchLean.Poisson.PTX.Flow.OperandWindow.Traversal
#print axioms PtxTorchLean.Poisson.PTX.Flow.OperandWindow.cut
#print axioms PtxTorchLean.Poisson.PTX.Flow.OperandWindow.exit_pc
#print axioms PtxTorchLean.Poisson.PTX.Flow.OperandWindow.traversal_runs
#print axioms PtxTorchLean.Poisson.PTX.DotInput.body
#print axioms PtxTorchLean.Poisson.PTX.DotInput.Valid
#print axioms PtxTorchLean.Poisson.PTX.DotInput.product
#print axioms PtxTorchLean.Poisson.PTX.DotInput.Stable
#print axioms PtxTorchLean.Poisson.PTX.DotInput.loaded
#print axioms PtxTorchLean.Poisson.PTX.DotInput.loads
#print axioms PtxTorchLean.Poisson.PTX.DotInput.loaded_eq
#print axioms PtxTorchLean.Poisson.PTX.DotInput.correct
#print axioms PtxTorchLean.Poisson.PTX.DotInput.exists_execution
#print axioms PtxTorchLean.Poisson.PTX.DotInput.cursor
#print axioms PtxTorchLean.Poisson.PTX.DotInput.progress
#print axioms PtxTorchLean.Poisson.PTX.DotInput.Checks.uneven_tail
#print axioms PtxTorchLean.Poisson.PTX.DotInput.Checks.empty_lane
#print axioms PtxTorchLean.Poisson.PTX.DotInput.Checks.wraparound
#print axioms PtxTorchLean.Poisson.PTX.DotInput.Checks.truncated_guard
#print axioms PtxTorchLean.Poisson.PTX.DotInput.Checks.initial
#print axioms PtxTorchLean.Poisson.PTX.DotInput.Checks.context
#print axioms PtxTorchLean.Poisson.PTX.DotInput.Checks.arbitrary_input
#print axioms PtxTorchLean.Poisson.PTX.DotInput.partialSum
#print axioms PtxTorchLean.Poisson.PTX.DotInput.input_correct
#print axioms PtxTorchLean.Poisson.PTX.DotInput.input_exists
#print axioms PtxTorchLean.Poisson.PTX.DotInput.traversal_exists
#print axioms PtxTorchLean.Poisson.PTX.DotInput.Arrays
#print axioms PtxTorchLean.Poisson.PTX.DotInput.address_at
#print axioms PtxTorchLean.Poisson.PTX.DotInput.arrays_valid
#print axioms PtxTorchLean.Poisson.PTX.DotInput.element
#print axioms PtxTorchLean.Poisson.PTX.DotInput.contribution_array
#print axioms PtxTorchLean.Poisson.PTX.DotInput.program
#print axioms PtxTorchLean.Poisson.PTX.DotInput.program_length
#print axioms PtxTorchLean.Poisson.PTX.DotInput.no_continuation
#print axioms PtxTorchLean.Poisson.PTX.DotInput.correct_loop
#print axioms PtxTorchLean.Poisson.PTX.DotInput.exists_loop
#print axioms PtxTorchLean.Poisson.PTX.DotInput.setupCode
#print axioms PtxTorchLean.Poisson.PTX.DotInput.setup
#print axioms PtxTorchLean.Poisson.PTX.DotInput.setup_sequence
#print axioms PtxTorchLean.Poisson.PTX.DotInput.lane_copy
#print axioms PtxTorchLean.Poisson.PTX.DotInput.setup_cursor
#print axioms PtxTorchLean.Poisson.PTX.DotInput.setup_zero
#print axioms PtxTorchLean.Poisson.PTX.DotInput.inputProgram
#print axioms PtxTorchLean.Poisson.PTX.DotInput.input_length
#print axioms PtxTorchLean.Poisson.PTX.DotInput.consume_setup
#print axioms PtxTorchLean.Poisson.PTX.DotInput.render
#print axioms PtxTorchLean.Poisson.PTX.DotInput.rendered
#print axioms PtxTorchLean.Poisson.PTX.DotInput.indices
#print axioms PtxTorchLean.Poisson.PTX.DotInput.atCursor
#print axioms PtxTorchLean.Poisson.PTX.DotInput.contribution
#print axioms PtxTorchLean.Poisson.PTX.DotInput.stable_refl
#print axioms PtxTorchLean.Poisson.PTX.DotInput.stable_trans
#print axioms PtxTorchLean.Poisson.PTX.DotInput.valid_at
#print axioms PtxTorchLean.Poisson.PTX.DotInput.product_at
#print axioms PtxTorchLean.Poisson.PTX.DotInput.test
#print axioms PtxTorchLean.Poisson.PTX.DotInput.traversal_correct
#print axioms PtxTorchLean.Poisson.PTX.Indexed.underlying_block
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeGuard.State
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeGuard.start
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeGuard.compared
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeGuard.branched
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeGuard.Step
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeGuard.Runs
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeGuard.Ready
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeGuard.CountsFit
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeGuard.initial
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeGuard.compare_value
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeGuard.branch_core
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeGuard.project_step
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeGuard.append
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeGuard.lift_step
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeGuard.lift
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeGuard.pending_sync
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeGuard.preserved
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeGuard.project
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Native.correct
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Native.exists_correct
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Native.safe
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Native.Instr
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Native.position
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Native.expand
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Native.code
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Native.pc
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Native.length
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Native.positions
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Native.located
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Native.counts
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Native.compare_fetch
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Native.branch_fetch
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Native.data_fetch
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Native.sync_fetch
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Native.sync_release
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Native.render
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Native.rendered
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Native.zero_displacement

#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.AddressReady
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.address_ready_initial
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.address_ready_early
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.input_address
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.tree_address
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.input_keeps_base
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.checked_tree
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.tree_base
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.tail_address
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.flow_address
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.sync_address
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.run_addresses
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.arrays_room
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.completed_input_correct
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.input_load_site
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.input_load_shape
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.input_no_index
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.input_address_exact
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.InputWord
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.input_access
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.OutputApart
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.output_address
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.input_word_separate
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.admitted_input
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.InputReady
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.input_ready_initial
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.count_word
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.input_footprint_step
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.input_observations
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.treeInstruction
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.tail
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.program
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.length
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.input_fetch
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.tree_fetch
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.tail_fetch
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.noIndex
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.no_index_loads
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.input_syntax
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.tree_targets
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.tail_targets
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.input_region
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.completed_input
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.render
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.rendered
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.inputSafe
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.input_safe
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.checked_tree_stores
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.global_store_site
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.stores_output
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.readonly_input
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.Instr
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.State
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.lane
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.update
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.Outcome
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.Step
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.Runs
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.waiting_blocks
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.halted_blocks
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.step_aligned
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.aligned
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.append
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.lane_update_self
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.lane_update_other
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.keeps
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.data_keeps
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.eval_keeps
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.step_lanes
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.runs_lanes
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.step_access_origin
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.access_prefix
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.prefix_step
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.prefix_run
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.continues
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.eval_live
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.observed_live
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.prefix_complete
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.targets
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.eval_upper
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.eval_lower
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.Region
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.Related
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.related_initial
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.no_prefix_sync
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.sync_prefix_unchanged
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.sync_monotone

#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.barrierSite
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.checked_barriers
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.checked_barrier_targets
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.barrier_fetch
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.barrier_stops
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.passed_barrier
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.PublicationAddress
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.publication_address_early
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.publication_address_late
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.publication_address_flow
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.publication_address_sync
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.publication_addresses
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.publication_registers
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.publication_location
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.publication_memory_bound
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.checked_tree_entry
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.outside_publication_targets
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.publication_prefix
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.publication_keeps
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.no_early_sync
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.PublicationLink
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.publication_track_step
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.publication_input
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.publication_fetch
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.publication_contents
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.continues_through_tree
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.returned_after_tree
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.returned_barriers
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.StopsAt
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.step_crosses_barrier
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.crossed_barrier
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.access_decompose
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.halting_eval
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.HaltedAfter
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.step_halted_after
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.runs_halted_after
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.step_history
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.runs_history
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.completed_arrivals
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.prefix_track
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.prefix_step_exact

#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.final_load_fetch
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.final_read_layout
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.final_read_source
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.Numeric.loads
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.Numeric.input_entry_table
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.Numeric.checked_numeric_targets
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.Numeric.entries
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.Numeric.update_tag
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.Numeric.stored
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.Numeric.outputLoads
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.Numeric.output_tag
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.Numeric.stored_output
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.Numeric.output_value
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.input_keeps_lane
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.input_keeps_scratch
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.checked_tree_registers
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.tree_keeps_setup
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.keeps_setup
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.SetupRegisters
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.setup_registers_flow
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.setup_registers
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.storeAddress
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.checked_store_fetch
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.store_fetch
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.checked_store_protection
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.protects_store
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.publication_across
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.checked_forward_targets
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.suffix_forward
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.addressCode
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.treeAddressTag
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.TreeAddress
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.tree_address_outside
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.checked_tree_address
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.tree_address_native
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.tree_address_flow
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.tree_address_sync
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.tree_addresses
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.treeLimit
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.treeGuard
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.TreeControl
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.tree_control_outside
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.checked_tree_control
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.tree_control_native
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.tree_control_flow
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.tree_control_sync
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.tree_control
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.Numeric.store_properties
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.Numeric.tree_publication_values
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.Numeric.partialInputs
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.Numeric.publication_value
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.storeSite
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.store_sites
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.checked_shared_stores
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.shared_store_site
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.shared_store_ownership
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.shared_stage_stores
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.stride
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.readPC
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.readOffset
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.readOperand
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.checked_read_fetch
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.read_fetch
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.checked_read_layout
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.tree_read_layout
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.stride_double
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.tree_read_source
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.ForwardFrom
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.eval_rank
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.step_rank
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.runs_rank
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.eval_access_pc
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.access_single
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.access_post
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.access_rank_bound
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.SuffixAccessOrder
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.access_order
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.access_unique
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.before_of_pc
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.event_prefix
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.step_arrival_origin
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.initialized_flow
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.initialized_sync
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.Protects
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.step_crosses_store
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.crossed_store
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.store_before_arrival
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.producer_across
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.access_after_barrier_index
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.own_writers_around
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.neighbor_writers_around
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.stage_own_read
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.stage_neighbor_read
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.Numeric.transfer
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.Numeric.tag
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.Numeric.Entries
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.Numeric.Invariant
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.Numeric.flow_ready
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.Numeric.step_invariant
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.Numeric.runs_invariant

#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness.complete
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness.CandidateEvent
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness.complete_candidate
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness.initial_wave
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.input_global_frame
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.input_access_read
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.input_recorded
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness.inputWords
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness.input_tree_candidate
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.InputEvent
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.input_wave
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.protects_output
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.output_exists
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness.stageTarget
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness.stage_wave
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness.Tail.code
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness.Tail.prepared
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness.Tail.finish
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness.Tail.events
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness.Tail.body_fetch
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness.Tail.block
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness.Tail.compared
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness.Tail.guarded
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness.Tail.guard_pc
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness.Tail.guard_core
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness.Tail.comparison
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness.Tail.guard_halted
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness.Tail.guard_run
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness.Tail.target
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness.Tail.records
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness.Tail.target_halted
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness.Tail.lane_run
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness.TailEvent
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness.tail_wave
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness.tree_candidate
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness.admitted
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness.compared
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness.guarded
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness.guarded_frame
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness.guarded_live
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness.guarded_pc
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness.guard_run
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness.ReadyAt
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness.initial_fetch
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness.update_fetch
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness.compare_fetch
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness.branch_fetch
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness.round_expected
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness.tree_producer
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness.final_producer
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness.Expected
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness.initial_expected
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness.update_expected
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Visibility.Repeated.construct_global_shared
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.memoryLayout
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.eval_layout
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.runs_layout
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.update_self
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.update_twice
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.lift_local
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.lift_block
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.afterRound
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.roundPrefix
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.prefix_dispatch
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.barrier_round_exists
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.Serial.allLanes
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.Serial.partialState
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.Serial.prefix_zero
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.Serial.prefix_all
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.Serial.prefix_next
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.Serial.run_lanes

#print axioms PtxTorchLean.Poisson.PTX.AffineUpdate.code
#print axioms PtxTorchLean.Poisson.PTX.AffineUpdate.scalar
#print axioms PtxTorchLean.Poisson.PTX.AffineUpdate.left
#print axioms PtxTorchLean.Poisson.PTX.AffineUpdate.loaded
#print axioms PtxTorchLean.Poisson.PTX.AffineUpdate.product
#print axioms PtxTorchLean.Poisson.PTX.AffineUpdate.result
#print axioms PtxTorchLean.Poisson.PTX.AffineUpdate.finish
#print axioms PtxTorchLean.Poisson.PTX.AffineUpdate.load_executes
#print axioms PtxTorchLean.Poisson.PTX.AffineUpdate.loads_eq
#print axioms PtxTorchLean.Poisson.PTX.AffineUpdate.executes
#print axioms PtxTorchLean.Poisson.PTX.AffineUpdate.correct
#print axioms PtxTorchLean.Poisson.PTX.AffineUpdate.entry
#print axioms PtxTorchLean.Poisson.PTX.AffineUpdate.entry_correct
#print axioms PtxTorchLean.Poisson.PTX.AffineUpdate.entry_exists
#print axioms PtxTorchLean.Poisson.PTX.AffineUpdate.inactive_correct
#print axioms PtxTorchLean.Poisson.PTX.AffineUpdate.inactive_exists
#print axioms PtxTorchLean.Poisson.PTX.AffineUpdate.rendered
#print axioms PtxTorchLean.Poisson.PTX.AffineUpdate.entry_length
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.GlobalPublication.NumericSafe
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.GlobalPublication.NumericPresent
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.GlobalPublication.numeric_apply_preserves
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.GlobalPublication.numeric_preserves
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.GlobalPublication.numeric_word
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.GlobalPublication.numeric_permuted
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.publication_outside
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.published_output
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness.complete_published
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.ZeroControl
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.zero_flow
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.zero_sync
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Dot.zero_returned_store
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Visibility.ThreadSourceChecks.read
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Visibility.ThreadSourceChecks.write
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Visibility.ThreadSourceChecks.events
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Visibility.ThreadSourceChecks.circular
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Visibility.ThreadSourceChecks.compatibility_alone
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Visibility.ThreadSourceChecks.circular_rejected
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Visibility.GlobalThreadSources
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Visibility.before_own_writes_initial
#print axioms PtxTorchLean.Poisson.PTX.Concurrent.Visibility.initial_thread_sources
#print axioms PtxTorchLean.Poisson.PTX.ScalarLoad.code
#print axioms PtxTorchLean.Poisson.PTX.ScalarLoad.addressed
#print axioms PtxTorchLean.Poisson.PTX.ScalarLoad.loaded
#print axioms PtxTorchLean.Poisson.PTX.ScalarLoad.executes
#print axioms PtxTorchLean.Poisson.PTX.ScalarLoad.block_eq
#print axioms PtxTorchLean.Poisson.PTX.VectorEntry.program
#print axioms PtxTorchLean.Poisson.PTX.VectorEntry.setup_run
#print axioms PtxTorchLean.Poisson.PTX.VectorEntry.inactive
#print axioms PtxTorchLean.Poisson.PTX.VectorEntry.completed_body
#print axioms PtxTorchLean.Poisson.PTX.VectorEntry.executes

#print axioms PtxTorchLean.Poisson.PTX.AffineUpdate.AccessAt
#print axioms PtxTorchLean.Poisson.PTX.AffineUpdate.access_step
#print axioms PtxTorchLean.Poisson.PTX.AffineUpdate.accesses
#print axioms PtxTorchLean.Poisson.PTX.AffineUpdate.no_index_step
#print axioms PtxTorchLean.Poisson.PTX.AffineUpdate.no_indices
#print axioms PtxTorchLean.Poisson.PTX.AffineUpdate.entry_linear
#print axioms PtxTorchLean.Poisson.PTX.AffineUpdate.AddressReady
#print axioms PtxTorchLean.Poisson.PTX.AffineUpdate.address_initial
#print axioms PtxTorchLean.Poisson.PTX.AffineUpdate.address_step
#print axioms PtxTorchLean.Poisson.PTX.AffineUpdate.Arena
#print axioms PtxTorchLean.Poisson.PTX.AffineUpdate.Arena.context
#print axioms PtxTorchLean.Poisson.PTX.AffineUpdate.Arena.start
#print axioms PtxTorchLean.Poisson.PTX.AffineUpdate.Arena.program
#print axioms PtxTorchLean.Poisson.PTX.AffineUpdate.Arena.slot
#print axioms PtxTorchLean.Poisson.PTX.AffineUpdate.Arena.value
#print axioms PtxTorchLean.Poisson.PTX.AffineUpdate.Arena.index
#print axioms PtxTorchLean.Poisson.PTX.AffineUpdate.Arena.live
#print axioms PtxTorchLean.Poisson.PTX.AffineUpdate.Arena.scalar_address
#print axioms PtxTorchLean.Poisson.PTX.AffineUpdate.Arena.vector_address
#print axioms PtxTorchLean.Poisson.PTX.AffineUpdate.Arena.setup_address
#print axioms PtxTorchLean.Poisson.PTX.AffineUpdate.Arena.vector_valid
#print axioms PtxTorchLean.Poisson.PTX.AffineUpdate.Arena.owners
#print axioms PtxTorchLean.Poisson.PTX.AffineUpdate.Arena.local_exists
#print axioms PtxTorchLean.Poisson.PTX.AffineUpdate.Arena.parallel_exists
#print axioms PtxTorchLean.Poisson.PTX.AffineUpdate.Arena.replay
#print axioms PtxTorchLean.Poisson.PTX.AffineUpdate.Arena.publication
#print axioms PtxTorchLean.Poisson.PTX.AffineUpdate.Arena.publication_outside
#print axioms PtxTorchLean.Poisson.PTX.AffineUpdate.Arena.local_value
#print axioms PtxTorchLean.Poisson.PTX.AffineUpdate.Arena.parallel_value
#print axioms PtxTorchLean.Poisson.PTX.AffineUpdate.BeforeStore
#print axioms PtxTorchLean.Poisson.PTX.AffineUpdate.before_store_step
#print axioms PtxTorchLean.Poisson.PTX.AffineUpdate.recorded_witness
#print axioms PtxTorchLean.Poisson.PTX.AffineUpdate.Arena.parallel_access
#print axioms PtxTorchLean.Poisson.PTX.AffineUpdate.Arena.read_value
#print axioms PtxTorchLean.Poisson.PTX.Flow.Parallel.native
#print axioms PtxTorchLean.Poisson.PTX.Flow.Parallel.native_update
#print axioms PtxTorchLean.Poisson.PTX.Flow.Parallel.native_run
#print axioms PtxTorchLean.Poisson.PTX.Flow.Parallel.linear_forward
#print axioms PtxTorchLean.Poisson.PTX.Flow.Parallel.before_of_pc
#print axioms PtxTorchLean.Poisson.PTX.Flow.Observed.eval_linear_pc
#print axioms PtxTorchLean.Poisson.PTX.Flow.Observed.word_lower
#print axioms PtxTorchLean.Poisson.PTX.Flow.Observed.step_future_frame
#print axioms PtxTorchLean.Poisson.PTX.Flow.Observed.replay_temporal

#print axioms PtxTorchLean.Poisson.PTX.Flow.scalar_segment
#print axioms PtxTorchLean.Poisson.PTX.Flow.scalar_sequence
#print axioms PtxTorchLean.Poisson.PTX.Flow.segment
#print axioms PtxTorchLean.Poisson.PTX.Flow.segment_linear
#print axioms PtxTorchLean.Poisson.PTX.Flow.segment_running
#print axioms PtxTorchLean.Poisson.PTX.Flow.peel_segment
#print axioms PtxTorchLean.Poisson.PTX.Flow.sequence_split
#print axioms PtxTorchLean.Poisson.PTX.Flow.sequence_pc
#print axioms PtxTorchLean.Poisson.PTX.Flow.sequence_running
#print axioms PtxTorchLean.Poisson.PTX.Flow.sequence_unique
#print axioms PtxTorchLean.Poisson.PTX.Flow.sequence_data_block
#print axioms PtxTorchLean.Poisson.PTX.PreconditionUpdate.one
#print axioms PtxTorchLean.Poisson.PTX.PreconditionUpdate.decode_one
#print axioms PtxTorchLean.Poisson.PTX.PreconditionUpdate.setupCode
#print axioms PtxTorchLean.Poisson.PTX.PreconditionUpdate.code
#print axioms PtxTorchLean.Poisson.PTX.PreconditionUpdate.diagonalLoaded
#print axioms PtxTorchLean.Poisson.PTX.PreconditionUpdate.prepared
#print axioms PtxTorchLean.Poisson.PTX.PreconditionUpdate.ready
#print axioms PtxTorchLean.Poisson.PTX.PreconditionUpdate.divisor
#print axioms PtxTorchLean.Poisson.PTX.PreconditionUpdate.result
#print axioms PtxTorchLean.Poisson.PTX.PreconditionUpdate.finish
#print axioms PtxTorchLean.Poisson.PTX.PreconditionUpdate.setup_trace
#print axioms PtxTorchLean.Poisson.PTX.PreconditionUpdate.ready_values
#print axioms PtxTorchLean.Poisson.PTX.PreconditionUpdate.ready_frame
#print axioms PtxTorchLean.Poisson.PTX.PreconditionUpdate.setup_plain
#print axioms PtxTorchLean.Poisson.PTX.PreconditionUpdate.code_segment
#print axioms PtxTorchLean.Poisson.PTX.PreconditionUpdate.state_result
#print axioms PtxTorchLean.Poisson.PTX.PreconditionUpdate.executes
#print axioms PtxTorchLean.Poisson.PTX.RegisterUpdate.code
#print axioms PtxTorchLean.Poisson.PTX.RegisterUpdate.left
#print axioms PtxTorchLean.Poisson.PTX.RegisterUpdate.loaded
#print axioms PtxTorchLean.Poisson.PTX.RegisterUpdate.product
#print axioms PtxTorchLean.Poisson.PTX.RegisterUpdate.result
#print axioms PtxTorchLean.Poisson.PTX.RegisterUpdate.finish
#print axioms PtxTorchLean.Poisson.PTX.RegisterUpdate.loads_execute
#print axioms PtxTorchLean.Poisson.PTX.RegisterUpdate.loads_eq
#print axioms PtxTorchLean.Poisson.PTX.RegisterUpdate.executes
#print axioms PtxTorchLean.Poisson.PTX.RegisterUpdate.state_result
#print axioms PtxTorchLean.Poisson.PTX.RegisterUpdate.finish_global
#print axioms PtxTorchLean.Poisson.PTX.RegisterUpdate.finish_regs
#print axioms PtxTorchLean.Poisson.PTX.RegisterUpdate.finish_address
#print axioms PtxTorchLean.Poisson.PTX.RegisterUpdate.finish_frame
#print axioms PtxTorchLean.Poisson.PTX.RegisterUpdate.finish_read
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.body
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.entry
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.coefficient
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.solution
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.residual
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.finish
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.body_segment
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.entry_length
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.AccessAt
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.access_step
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.accesses
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.index_step
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.index_accesses
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.entry_linear
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.AddressReady
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.address_initial
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.address_step
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.Field
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.Arena
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.Arena.context
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.Arena.start
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.Arena.program
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.Arena.slot
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.Arena.index
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.Arena.live
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.Arena.scalar_address
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.Arena.vector_address
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.Arena.boundary_address
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.Arena.setup_address
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.Arena.setup_boundary
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.Arena.owners
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.Arena.alpha_disjoint
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.Arena.boundary_disjoint
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.Arena.overlap_owner
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.Arena.vector_valid
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.Arena.local_valid
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.Arena.local_separate
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.correct
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.entry_correct
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.body_exists
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.entry_exists
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.inactive
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.inactive_exists
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.storePC
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.readPC
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.Arena.access_shape
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.Arena.parallel_access
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.Arena.parallel_index
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.SameGeometry
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.Valid
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.SameGeometry.address
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.SameGeometry.mask
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.SameGeometry.valid
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.coefficient_geometry
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.solution_geometry
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.residual_geometry
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.coefficient_global
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.coefficient_word
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.solution_global
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.solution_word
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.residual_global
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.residual_word
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.finish_global
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.Separate
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.alphaValue
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.vectorValue
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.xValue
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.rValue
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.zValue
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.x_value
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.r_value
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.divisor_value
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.z_value
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.stored_words
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.Arena.value
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.Arena.replay
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.Arena.publication
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.Arena.local_value
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.Arena.parallel_value
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.Arena.publication_outside
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.Arena.local_exists
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.Arena.parallel_exists
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.Arena.Pending
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.Arena.pending_initial
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.Arena.pending_advance
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.Arena.pending_step
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.Arena.recorded_witness
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.Arena.read_value
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.Arena.index_value
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.Arena.future_apart
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.Arena.index_apart
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.state_result
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.instruction
#print axioms PtxTorchLean.Poisson.PTX.UpdateXRZ.rendered
#print axioms PtxTorchLean.Poisson.PTX.VectorFlowEntry.program
#print axioms PtxTorchLean.Poisson.PTX.VectorFlowEntry.setup_run
#print axioms PtxTorchLean.Poisson.PTX.VectorFlowEntry.inactive
#print axioms PtxTorchLean.Poisson.PTX.VectorFlowEntry.completed_body
#print axioms PtxTorchLean.Poisson.PTX.VectorFlowEntry.executes

#print axioms PtxTorchLean.Poisson.PTX.ArrayArena
#print axioms PtxTorchLean.Poisson.PTX.ArrayArena.context
#print axioms PtxTorchLean.Poisson.PTX.ArrayArena.start
#print axioms PtxTorchLean.Poisson.PTX.ArrayArena.slot
#print axioms PtxTorchLean.Poisson.PTX.ArrayArena.index
#print axioms PtxTorchLean.Poisson.PTX.ArrayArena.live
#print axioms PtxTorchLean.Poisson.PTX.ArrayArena.vector_address
#print axioms PtxTorchLean.Poisson.PTX.ArrayArena.boundary_address
#print axioms PtxTorchLean.Poisson.PTX.ArrayArena.setup_address
#print axioms PtxTorchLean.Poisson.PTX.ArrayArena.setup_boundary
#print axioms PtxTorchLean.Poisson.PTX.ArrayArena.owners
#print axioms PtxTorchLean.Poisson.PTX.ArrayArena.boundary_disjoint
#print axioms PtxTorchLean.Poisson.PTX.ArrayArena.overlap_owner
#print axioms PtxTorchLean.Poisson.PTX.ArrayArena.vector_valid
#print axioms PtxTorchLean.Poisson.PTX.ArrayArena.boundary_valid
#print axioms PtxTorchLean.Poisson.PTX.DividePair.code
#print axioms PtxTorchLean.Poisson.PTX.DividePair.first
#print axioms PtxTorchLean.Poisson.PTX.DividePair.finish
#print axioms PtxTorchLean.Poisson.PTX.DividePair.result
#print axioms PtxTorchLean.Poisson.PTX.DividePair.executes
#print axioms PtxTorchLean.Poisson.PTX.DividePair.state_result
#print axioms PtxTorchLean.Poisson.PTX.DividePair.finish_global
#print axioms PtxTorchLean.Poisson.PTX.DividePair.finish_frame
#print axioms PtxTorchLean.Poisson.PTX.RestartVectors.prefixCode
#print axioms PtxTorchLean.Poisson.PTX.RestartVectors.body
#print axioms PtxTorchLean.Poisson.PTX.RestartVectors.entry
#print axioms PtxTorchLean.Poisson.PTX.RestartVectors.copied
#print axioms PtxTorchLean.Poisson.PTX.RestartVectors.ready
#print axioms PtxTorchLean.Poisson.PTX.RestartVectors.finish
#print axioms PtxTorchLean.Poisson.PTX.RestartVectors.Valid
#print axioms PtxTorchLean.Poisson.PTX.RestartVectors.copied_mask
#print axioms PtxTorchLean.Poisson.PTX.RestartVectors.prefix_trace
#print axioms PtxTorchLean.Poisson.PTX.RestartVectors.prefix_plain
#print axioms PtxTorchLean.Poisson.PTX.RestartVectors.body_segment
#print axioms PtxTorchLean.Poisson.PTX.RestartVectors.ready_frame
#print axioms PtxTorchLean.Poisson.PTX.RestartVectors.entry_length
#print axioms PtxTorchLean.Poisson.PTX.RestartVectors.AccessAt
#print axioms PtxTorchLean.Poisson.PTX.RestartVectors.access_step
#print axioms PtxTorchLean.Poisson.PTX.RestartVectors.accesses
#print axioms PtxTorchLean.Poisson.PTX.RestartVectors.index_step
#print axioms PtxTorchLean.Poisson.PTX.RestartVectors.index_accesses
#print axioms PtxTorchLean.Poisson.PTX.RestartVectors.entry_linear
#print axioms PtxTorchLean.Poisson.PTX.RestartVectors.AddressReady
#print axioms PtxTorchLean.Poisson.PTX.RestartVectors.address_initial
#print axioms PtxTorchLean.Poisson.PTX.RestartVectors.address_step
#print axioms PtxTorchLean.Poisson.PTX.RestartVectors.Field
#print axioms PtxTorchLean.Poisson.PTX.RestartVectors.Arena
#print axioms PtxTorchLean.Poisson.PTX.RestartVectors.Arena.program
#print axioms PtxTorchLean.Poisson.PTX.RestartVectors.Arena.local_valid
#print axioms PtxTorchLean.Poisson.PTX.RestartVectors.Arena.local_separate
#print axioms PtxTorchLean.Poisson.PTX.RestartVectors.Arena.access_shape
#print axioms PtxTorchLean.Poisson.PTX.RestartVectors.Arena.parallel_access
#print axioms PtxTorchLean.Poisson.PTX.RestartVectors.Arena.parallel_index
#print axioms PtxTorchLean.Poisson.PTX.RestartVectors.Separate
#print axioms PtxTorchLean.Poisson.PTX.RestartVectors.quotient
#print axioms PtxTorchLean.Poisson.PTX.RestartVectors.divisor_value
#print axioms PtxTorchLean.Poisson.PTX.RestartVectors.ready_result
#print axioms PtxTorchLean.Poisson.PTX.RestartVectors.correct
#print axioms PtxTorchLean.Poisson.PTX.RestartVectors.entry_correct
#print axioms PtxTorchLean.Poisson.PTX.RestartVectors.entry_exists
#print axioms PtxTorchLean.Poisson.PTX.RestartVectors.inactive
#print axioms PtxTorchLean.Poisson.PTX.RestartVectors.inactive_exists
#print axioms PtxTorchLean.Poisson.PTX.RestartVectors.Arena.local_exists
#print axioms PtxTorchLean.Poisson.PTX.RestartVectors.Arena.parallel_exists
#print axioms PtxTorchLean.Poisson.PTX.RestartVectors.Arena.Inputs
#print axioms PtxTorchLean.Poisson.PTX.RestartVectors.Arena.inputs_initial
#print axioms PtxTorchLean.Poisson.PTX.RestartVectors.Arena.inputs_step
#print axioms PtxTorchLean.Poisson.PTX.RestartVectors.Arena.quotient
#print axioms PtxTorchLean.Poisson.PTX.RestartVectors.Arena.separated
#print axioms PtxTorchLean.Poisson.PTX.RestartVectors.Arena.publication
#print axioms PtxTorchLean.Poisson.PTX.RestartVectors.Arena.local_correct
#print axioms PtxTorchLean.Poisson.PTX.RestartVectors.Arena.parallel_correct
#print axioms PtxTorchLean.Poisson.PTX.RestartVectors.Arena.publication_outside
#print axioms PtxTorchLean.Poisson.PTX.RestartVectors.Arena.recorded_witness
#print axioms PtxTorchLean.Poisson.PTX.RestartVectors.ready_address
#print axioms PtxTorchLean.Poisson.PTX.RestartVectors.state_result
#print axioms PtxTorchLean.Poisson.PTX.RestartVectors.body_exists
#print axioms PtxTorchLean.Poisson.PTX.RestartVectors.ready_word
#print axioms PtxTorchLean.Poisson.PTX.RestartVectors.ready_divisor
#print axioms PtxTorchLean.Poisson.PTX.RestartVectors.finish_global
#print axioms PtxTorchLean.Poisson.PTX.RestartVectors.rendered
#print axioms PtxTorchLean.Poisson.PTX.VectorCopy.code
#print axioms PtxTorchLean.Poisson.PTX.VectorCopy.loaded
#print axioms PtxTorchLean.Poisson.PTX.VectorCopy.finish
#print axioms PtxTorchLean.Poisson.PTX.VectorCopy.executes
#print axioms PtxTorchLean.Poisson.PTX.VectorCopy.block_eq
#print axioms PtxTorchLean.Poisson.PTX.VectorCopy.finish_global
#print axioms PtxTorchLean.Poisson.PTX.VectorCopy.finish_frame
#print axioms PtxTorchLean.Poisson.PTX.VectorCopy.finish_address

#print axioms PtxTorchLean.Poisson.PTX.Initialize.prefixCode
#print axioms PtxTorchLean.Poisson.PTX.Initialize.body
#print axioms PtxTorchLean.Poisson.PTX.Initialize.entry
#print axioms PtxTorchLean.Poisson.PTX.Initialize.maskLoaded
#print axioms PtxTorchLean.Poisson.PTX.Initialize.loadLoaded
#print axioms PtxTorchLean.Poisson.PTX.Initialize.masked
#print axioms PtxTorchLean.Poisson.PTX.Initialize.copied
#print axioms PtxTorchLean.Poisson.PTX.Initialize.diagonalLoaded
#print axioms PtxTorchLean.Poisson.PTX.Initialize.ready
#print axioms PtxTorchLean.Poisson.PTX.Initialize.divided
#print axioms PtxTorchLean.Poisson.PTX.Initialize.finish
#print axioms PtxTorchLean.Poisson.PTX.Initialize.Valid
#print axioms PtxTorchLean.Poisson.PTX.Initialize.prefix_plain
#print axioms PtxTorchLean.Poisson.PTX.Initialize.body_segment
#print axioms PtxTorchLean.Poisson.PTX.Initialize.entry_length
#print axioms PtxTorchLean.Poisson.PTX.Initialize.AccessAt
#print axioms PtxTorchLean.Poisson.PTX.Initialize.access_step
#print axioms PtxTorchLean.Poisson.PTX.Initialize.accesses
#print axioms PtxTorchLean.Poisson.PTX.Initialize.index_step
#print axioms PtxTorchLean.Poisson.PTX.Initialize.index_accesses
#print axioms PtxTorchLean.Poisson.PTX.Initialize.entry_linear
#print axioms PtxTorchLean.Poisson.PTX.Initialize.AddressReady
#print axioms PtxTorchLean.Poisson.PTX.Initialize.address_initial
#print axioms PtxTorchLean.Poisson.PTX.Initialize.address_step
#print axioms PtxTorchLean.Poisson.PTX.Initialize.Field
#print axioms PtxTorchLean.Poisson.PTX.Initialize.Arena
#print axioms PtxTorchLean.Poisson.PTX.Initialize.Arena.program
#print axioms PtxTorchLean.Poisson.PTX.Initialize.Arena.local_valid
#print axioms PtxTorchLean.Poisson.PTX.Initialize.Arena.local_separate
#print axioms PtxTorchLean.Poisson.PTX.Initialize.Arena.access_shape
#print axioms PtxTorchLean.Poisson.PTX.Initialize.Arena.parallel_access
#print axioms PtxTorchLean.Poisson.PTX.Initialize.Arena.parallel_index
#print axioms PtxTorchLean.Poisson.PTX.Initialize.Separate
#print axioms PtxTorchLean.Poisson.PTX.Initialize.correct
#print axioms PtxTorchLean.Poisson.PTX.Initialize.entry_correct
#print axioms PtxTorchLean.Poisson.PTX.Initialize.entry_exists
#print axioms PtxTorchLean.Poisson.PTX.Initialize.inactive
#print axioms PtxTorchLean.Poisson.PTX.Initialize.inactive_exists
#print axioms PtxTorchLean.Poisson.PTX.Initialize.Arena.local_exists
#print axioms PtxTorchLean.Poisson.PTX.Initialize.Arena.parallel_exists
#print axioms PtxTorchLean.Poisson.PTX.Initialize.Arena.Inputs
#print axioms PtxTorchLean.Poisson.PTX.Initialize.Arena.inputs_initial
#print axioms PtxTorchLean.Poisson.PTX.Initialize.Arena.inputs_step
#print axioms PtxTorchLean.Poisson.PTX.Initialize.Arena.loadWord
#print axioms PtxTorchLean.Poisson.PTX.Initialize.Arena.quotient
#print axioms PtxTorchLean.Poisson.PTX.Initialize.Arena.separated
#print axioms PtxTorchLean.Poisson.PTX.Initialize.Arena.publication
#print axioms PtxTorchLean.Poisson.PTX.Initialize.Arena.local_correct
#print axioms PtxTorchLean.Poisson.PTX.Initialize.Arena.parallel_correct
#print axioms PtxTorchLean.Poisson.PTX.Initialize.Arena.publication_outside
#print axioms PtxTorchLean.Poisson.PTX.Initialize.masked_frame
#print axioms PtxTorchLean.Poisson.PTX.Initialize.copied_frame
#print axioms PtxTorchLean.Poisson.PTX.Initialize.ready_frame
#print axioms PtxTorchLean.Poisson.PTX.Initialize.ready_address
#print axioms PtxTorchLean.Poisson.PTX.Initialize.prefix_trace
#print axioms PtxTorchLean.Poisson.PTX.Initialize.Arena.recorded_witness
#print axioms PtxTorchLean.Poisson.PTX.Initialize.divided_address
#print axioms PtxTorchLean.Poisson.PTX.Initialize.divided_frame
#print axioms PtxTorchLean.Poisson.PTX.Initialize.state_result
#print axioms PtxTorchLean.Poisson.PTX.Initialize.body_exists
#print axioms PtxTorchLean.Poisson.PTX.Initialize.instruction
#print axioms PtxTorchLean.Poisson.PTX.Initialize.rendered
#print axioms PtxTorchLean.Poisson.PTX.Initialize.loadWord
#print axioms PtxTorchLean.Poisson.PTX.Initialize.masked_word
#print axioms PtxTorchLean.Poisson.PTX.Initialize.copied_global
#print axioms PtxTorchLean.Poisson.PTX.Initialize.ready_word
#print axioms PtxTorchLean.Poisson.PTX.Initialize.ready_divisor
#print axioms PtxTorchLean.Poisson.PTX.Initialize.quotient
#print axioms PtxTorchLean.Poisson.PTX.Initialize.ready_result
#print axioms PtxTorchLean.Poisson.PTX.Initialize.finish_global
#print axioms PtxTorchLean.Poisson.PTX.StorePair.code
#print axioms PtxTorchLean.Poisson.PTX.StorePair.first
#print axioms PtxTorchLean.Poisson.PTX.StorePair.finish
#print axioms PtxTorchLean.Poisson.PTX.StorePair.executes
#print axioms PtxTorchLean.Poisson.PTX.StorePair.block_eq
#print axioms PtxTorchLean.Poisson.PTX.StorePair.finish_global
#print axioms PtxTorchLean.Poisson.PTX.StorePair.finish_frame
#print axioms PtxTorchLean.Poisson.PTX.StoreZero.code
#print axioms PtxTorchLean.Poisson.PTX.StoreZero.finish
#print axioms PtxTorchLean.Poisson.PTX.StoreZero.executes
#print axioms PtxTorchLean.Poisson.PTX.StoreZero.block_eq
#print axioms PtxTorchLean.Poisson.PTX.StoreZero.finish_global
#print axioms PtxTorchLean.Poisson.PTX.StoreZero.finish_frame
