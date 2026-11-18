module

public import Silmaril.Formats.Cbor.Drisl.Number.Defs
public import Silmaril.Formats.JsonWithBytes.Traverse.Defs

@[expose] public section

namespace Silmaril.Formats.Cbor.Drisl

def mapNumber? {Input Output : Type} (number : Input → Option Output) :
    JsonWithBytes.Scalar Input → Option (JsonWithBytes.Scalar Output)
  | .null => some .null
  | .bool value => some (.bool value)
  | .string value => some (.string value)
  | .bytes value => some (.bytes value)
  | .number value => .number <$> number value

def removeLinks? {Numeric Link : Type} {index : JsonIx}
    (value : RawSyn String (Scalar Numeric Link) index) :
    Option (RawSyn String (JsonWithBytes.Scalar Numeric) index) :=
  JsonWithBytes.traverse? some (fun | .data scalar => some scalar | .link _ => none) value

def fromJsonWithBytes? {Link : Type} (value : JsonWithBytes.Ordered) : Option (Ordered Link) :=
  JsonWithBytes.traverse? some (fun scalar => .data <$> mapNumber? Number.ofDecimal? scalar) value

def jsonWithBytesI64? (value : JsonWithBytes.Ordered) : Option JsonWithBytes.OrderedI64 :=
  JsonWithBytes.traverse? some (mapNumber? decimalI64?) value

def narrowATProto? {Link : Type} (value : Ordered Link) : Option (OrderedATProto Link) :=
  JsonWithBytes.traverse? some (fun
    | .link cid => some (.link cid)
    | .data scalar => .data <$> mapNumber? (fun
        | .integer integral => int64? integral.toInt
        | .float _ => none) scalar) value

end Silmaril.Formats.Cbor.Drisl
