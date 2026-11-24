module

import Silmaril.Containers.SqliteVfs.Thms
import Silmaril.Machine.SqliteVfs.Thms

namespace Silmaril.Containers.SqliteVfs

open Silmaril.Machine.SqliteVfs

private def initial : FileState := { bytes := [10, 20, 30] }
private def handle : Handle := ⟨0⟩
private def capacity : Nat := 6

private def roTrace : Trace := [
  ⟨.openFile .readWrite, .error .cannotOpen⟩,
  ⟨.openFile .readOnly, .ok handle⟩,
  ⟨.openFile .readOnly, .error .cannotOpen⟩,
  ⟨.read handle 1 2, .ok [20, 30]⟩,
  ⟨.read handle 2 3, .shortRead [30, 0, 0]⟩,
  ⟨.read handle 7 2, .shortRead [0, 0]⟩,
  ⟨.write handle 0 [14], .error .readOnly⟩,
  ⟨.truncate handle 0, .error .readOnly⟩,
  ⟨.read handle (-1) 1, .error .invalidRange⟩,
  ⟨.read handle 0 0, .error .invalidRange⟩,
  ⟨.read handle 0 2147483648, .error .invalidRange⟩,
  ⟨.read handle 9223372036854775807 1, .error .invalidRange⟩,
  ⟨.close handle, .ok ()⟩,
  ⟨.openFile .readOnly, .ok ⟨1⟩⟩,
  ⟨.fileSize handle, .error .invalidHandle⟩,
  ⟨.fileSize ⟨1⟩, .ok 3⟩
]

private theorem roValid :
    Trace.Valid (readOnly capacity) initial roTrace
      { initial with openMode := some .readOnly, generation := 1 } := by
  repeat (first | apply Trace.Valid.cons rfl | exact Trace.Valid.nil _)

example : (runtime (readOnly capacity)).beh initial (.blocked (encode roTrace)) :=
  blocked_iff.mpr ⟨_, _, roValid, rfl⟩

private def rwTrace : Trace := [
  ⟨.openFile .readOnly, .ok handle⟩,
  ⟨.write handle 0 [9], .error .readOnly⟩,
  ⟨.close handle, .ok ()⟩,
  ⟨.openFile .readWrite, .ok ⟨1⟩⟩,
  ⟨.write ⟨1⟩ 1 [11], .ok ()⟩,
  ⟨.write ⟨1⟩ 4 [99], .ok ()⟩,
  ⟨.read ⟨1⟩ 0 5, .ok [10, 11, 30, 0, 99]⟩,
  ⟨.write ⟨1⟩ 6 [1], .error .full⟩,
  ⟨.write ⟨1⟩ 0 [], .error .invalidRange⟩,
  ⟨.truncate ⟨1⟩ 7, .error .full⟩,
  ⟨.truncate ⟨1⟩ 2, .ok ()⟩,
  ⟨.truncate ⟨1⟩ 4, .ok ()⟩,
  ⟨.fileSize ⟨1⟩, .ok 4⟩,
  ⟨.read ⟨1⟩ 0 5, .shortRead [10, 11, 0, 0, 0]⟩,
  ⟨.truncate ⟨1⟩ (-1), .error .invalidRange⟩
]

private def rwFinal : FileState := ⟨[10, 11, 0, 0], some .readWrite, 1⟩

private theorem rwValid : Trace.Valid (readWrite capacity) initial rwTrace rwFinal := by
  repeat (first | apply Trace.Valid.cons rfl | exact Trace.Valid.nil _)

example : (runtime (readWrite capacity)).beh initial (.blocked (encode rwTrace)) :=
  blocked_iff.mpr ⟨_, _, rwValid, rfl⟩

example : (machine (readWrite capacity)).Exec Mach.seqPolicy (.idle initial)
    (encode rwTrace ++ [.recv (.close ⟨1⟩)]) (.pending rwFinal (.close ⟨1⟩)) :=
  exec_iff.mpr ⟨_, _, rwValid, .inr ⟨_, rfl, rfl⟩⟩

private def badTrace : Trace := [
  ⟨.openFile .readOnly, .ok handle⟩,
  ⟨.read handle 2 3, .shortRead [30, 255, 255]⟩
]

example : (runtime (badShortRead capacity)).beh initial (.blocked (encode badTrace)) := by
  refine blocked_iff.mpr ⟨badTrace, { initial with openMode := some .readOnly }, ?_, rfl⟩
  exact .cons rfl (.cons rfl (.nil _))

#print axioms readOnly_lawful
#print axioms readWrite_lawful
#print axioms backing_trace_bounds
#print axioms readOnly_trace_bytes
#print axioms overwrite_length
#print axioms resize_length
#print axioms zeroFill_of_readLaw
#print axioms bad_preserves_readOnly
#print axioms bad_violates_zeroFill
#print axioms bad_not_readOnlyProfile
#print axioms exec_iff
#print axioms blocked_iff

end Silmaril.Containers.SqliteVfs
