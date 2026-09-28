#
# Generate values from model
#
import copy
import json
import math
import re
import re._parser as _parser

from .mtypes import ModelType, ModelArray, ModelObject, Jsonable, JsonScalar, ModelError
from .model import JsonModel
from .resolver import Resolver
from . import analyze
from .predefs import (MODEL_PREDEFS, PREDEFS, PREDEF_RE, STR_MODEL_PREDEFS,
                      BOOL_MODEL_PREDEFS, INT_MODEL_PREDEFS, FLOAT_MODEL_PREDEFS)
from .python import PYTHON_RUNTIME_PREDEFS
from .runtime import support
from .runtime.types import EntryCheckFun
from .utils import cst, is_a_simple_object

_MODEL_NAME_RE = re.compile(r"^[^\s\[\]'\"]+$")
_CATEGORIES = {
    _parser.CATEGORY_DIGIT: "0",
    _parser.CATEGORY_WORD: "a",
    _parser.CATEGORY_SPACE: " ",
}
_ANY_CHAR = "a"
_ITEM_VARIANTS = 2
_NAME_CHARS = "abcdefghijklmnopqrstuvwxyz"
_ANY_NAME_PREDEFS = {"$ANY", "$STRING"}
_NO_NAME_PREDEFS = {"$NULL", "$NONE"} | BOOL_MODEL_PREDEFS | INT_MODEL_PREDEFS | FLOAT_MODEL_PREDEFS
_OPERATORS = {"@", "|", "&", "^", "!", "=", "!=", "<", "<=", ">", ">="}
_QUOTED_OPS = _OPERATORS - {"@"}
_COMPARISONS = {"=", "!=", "<", "<=", ">", ">="}
_CONSTRAINTS = _COMPARISONS | {"!"}
_INT_VIOLATIONS = {
    ">=": lambda n: math.ceil(n) - 1, ">": lambda n: math.floor(n),
    "<=": lambda n: math.floor(n) + 1, "<": lambda n: math.ceil(n),
    "=": lambda n: math.floor(n) + 1, "!=": lambda n: n,
}
_FLOAT_VIOLATIONS = {
    ">=": lambda n: n - 1.0, ">": lambda n: float(n),
    "<=": lambda n: n + 1.0, "<": lambda n: float(n),
    "=": lambda n: n + 1.0, "!=": lambda n: float(n),
}
_INT_BOUNDS = {
    ">=": lambda n: math.ceil(n), ">": lambda n: math.floor(n) + 1,
    "<=": lambda n: math.floor(n), "<": lambda n: math.ceil(n) - 1,
    "=": lambda n: math.floor(n), "!=": lambda n: math.floor(n) + 1,
}
_INT_MIRRORS = {"!=": lambda n: math.floor(n) - 1}
_FLOAT_BOUNDS = {
    ">=": lambda n: float(n), "<=": lambda n: float(n), "=": lambda n: float(n),
}
_PI = 3.1415927
_TYPE_VIOLATIONS = [None, True, 0, "", [], {}]
_ROOT_TYPES = [None, True, False, -42, _PI, "", "unexpected", [], [1, "expected"], {}, {"un": "expected"}]
_EXTRA_NAMES = ["no-such-prop", "no-such-property", "no-such-property1"]
_UINT_PREDEFS = {"$U32", "$U64"}
_PREDEFS = {
    "$ANY": {}, "$NULL": None,
    "$BOOL": False, "$BOOLEAN": False,
    "$INT": 0, "$INTEGER": 0, "$I32": 0, "$I64": 0, "$U32": 0, "$U64": 0,
    "$FLOAT": 0.0, "$F32": 0.0, "$F64": 0.0, "$NUMBER": 0,
    "$STRING": "", "$REGEX": "", "$EXREG": "", "$JSONPT": "",
    "$DATE": "1970-01-01", "$TIME": "00:00:00", "$TIMETZ": "00:00:00+00:00",
    "$DATETIME": "1970-01-01T00:00:00", "$DURATION": "PT0S",
    "$UUID": "00000000-0000-0000-0000-000000000000", "$CARD": "4111111111111111",
    "$IP4": "0.0.0.0", "$IP6": "::", "$HOST": "json-model.org",
    "$ETH": "00:00:00:00:00:00",
    "$URL": "https://json.org/", "$URI": "https://json.org/",
    "$URL_REL": "/", "$EMAIL": "susie@json.org",
    "$JSON": "null", "$SEMVER": "0.0.0",
}

_PREDEF_VIOLATIONS = {
    "$U32": -1, "$U64": -1,
    "$REGEX": "[ not a regex", "$EXREG": "[ not a exreg", "$JSONPT": "not a jsonpt",
    "$DATE": "not a date", "$TIME": "not a time", "$TIMETZ": "not a timetz",
    "$DATETIME": "not a datetime", "$DURATION": "not a duration",
    "$UUID": "not a uuid", "$CARD": "not a card",
    "$IP4": "not a ip4", "$IP6": "not a ip6", "$HOST": "not a host",
    "$ETH": "not a eth",
    "$URL": "not a url", "$URI": "not a uri",
    "$URL_REL": "not a relative url", "$EMAIL": "not an email address",
    "$JSON": "not a json value", "$SEMVER": "not a version",
}

class UnsupportedValue(Exception):
    """No value could be generated for this model."""
    pass

class Vacuous(UnsupportedValue):
    """The model is inherently empty or holds no constraint."""
    pass

def _value_key(value: Jsonable) -> str:
    """Comparison key of a generated value."""
    return json.dumps(value, sort_keys=True)

def _brief(model: ModelType, size: int = 60) -> str:
    """Short readable rendering of a model, for failure messages."""
    text = repr(model)
    return text if len(text) <= size else text[:size] + "..."

def _joined(reasons: list[str], limit: int = 8) -> str:
    """Distinct failure reasons, capped for readability."""
    kept = list(dict.fromkeys(reasons))
    text = "; ".join(kept[:limit])
    return text if len(kept) <= limit else f"{text}; and {len(kept) - limit} more"

def _simplest_scalar(model: ModelType) -> JsonScalar:
    """Simplest value for a scalar type inference model."""
    match model:
        case None:
            return None
        case bool():
            return False
        case int():
            return 1 if model == 1 else 0
        case float():
            if model == 0.0:
                return 0.0
            return _PI if model == 1.0 else -_PI
        case _:
            assert False, f"not a scalar model: {model}"

def _regex_char(item) -> str:
    """Simplest character for a regex character class item."""
    op, av = item
    if op is _parser.LITERAL:
        return chr(av)
    elif op is _parser.RANGE:
        return chr(av[0])
    elif op is _parser.CATEGORY and av in _CATEGORIES:
        return _CATEGORIES[av]
    else:
        raise UnsupportedValue(f"unsupported regex character class item: {op}")

def _regex_walk(pattern) -> str:
    """Simplest string matching a parsed regex."""
    value = ""
    for op, av in pattern:
        if op is _parser.LITERAL:
            value += chr(av)
        elif op is _parser.AT:
            pass
        elif op is _parser.ANY:
            value += _ANY_CHAR
        elif op is _parser.IN:
            value += _regex_char(av[0])
        elif op is _parser.MAX_REPEAT or op is _parser.MIN_REPEAT:
            repeat, _, body = av
            value += _regex_walk(body) * repeat
        elif op is _parser.BRANCH:
            value += _regex_walk(av[1][0])
        elif op is _parser.SUBPATTERN:
            value += _regex_walk(av[3])
        else:
            raise UnsupportedValue(f"unsupported regex construct: {op}")
    return value

def _simplest_regex(model: str) -> str:
    """Simplest value for a regex model."""
    assert "/" in model[1:], f"invalid regex model: {model}"
    pattern, opts = model[1:].rsplit("/", 1)
    if "X" in opts:
        raise UnsupportedValue(f"unsupported extended regex model: {model}")
    source = f"(?{opts}){pattern}" if opts else pattern
    try:
        parsed, compiled = _parser.parse(source), re.compile(source)
    except re.error as e:
        raise UnsupportedValue(f"invalid regex model {model}: {e}")
    value = _regex_walk(parsed)
    if compiled.search(value) is None:
        raise UnsupportedValue(f"no value generated for regex model: {model}")
    else:
        return value

def _simplest_predef(model: str, jm: JsonModel, seen: frozenset[str]) -> Jsonable:
    """Simplest value for a predefined model or a reference."""
    if model in _PREDEFS:
        value = _PREDEFS[model]
        return copy.copy(value) if isinstance(value, (dict, list)) else value
    elif model == "$NONE":
        raise Vacuous("no value exists for model: $NONE")
    elif model in MODEL_PREDEFS:
        raise UnsupportedValue(f"unsupported predefined model: {model}")
    else:
        try:
            ja = jm.resolveRef(model, [])
        except (ModelError, AssertionError) as e:
            raise UnsupportedValue(f"cannot resolve {model}: {e}")
        if ja._url in seen:
            raise UnsupportedValue(f"no finite value for recursive model: {model}")
        else:
            return simplest(ja._model, ja, seen | {ja._url})

def _simplest_array(model: ModelArray, jm: JsonModel, seen: frozenset[str]) -> Jsonable:
    """Simplest value for an array or tuple model."""
    items = [(i, m) for i, m in enumerate(model)
             if not (isinstance(m, str) and m.startswith("#"))]
    if len(items) <= 1:
        return []
    values: list[Jsonable] = []
    for index, item in items:
        try:
            values.append(simplest(item, jm, seen))
        except UnsupportedValue as e:
            raise type(e)(f"{index}: {e}")
    return values

def _numeric_low(model: ModelType) -> int|float|None:
    """Smallest value allowed by a numeric model, None if unbounded below."""
    if isinstance(model, bool):
        return None
    elif isinstance(model, (int, float)):
        return None if model in (-1, -1.0) else model
    elif isinstance(model, str) and model in _UINT_PREDEFS:
        return 0
    else:
        return None

def _bounds(ops: ModelObject, step: int|float,
            low: int|float|None) -> tuple[int|float|None, int|float|None]:
    """Lower and upper bounds implied by comparison constraints."""
    lo, hi = low, None
    if "=" in ops:
        lo = hi = ops["="]
    if ">=" in ops:
        lo = ops[">="] if lo is None else max(lo, ops[">="])
    if ">" in ops:
        bound = ops[">"] + step
        lo = bound if lo is None else max(lo, bound)
    if "<=" in ops:
        hi = ops["<="] if hi is None else min(hi, ops["<="])
    if "<" in ops:
        bound = ops["<"] - step
        hi = bound if hi is None else min(hi, bound)
    return lo, hi

def _pick(lo: int|float|None, hi: int|float|None, ops: ModelObject,
          step: int|float, zero: int|float) -> int|float:
    """Simplest number within bounds, avoiding an excluded value."""
    value = zero
    if lo is not None and value < lo:
        value = lo
    if hi is not None and value > hi:
        value = hi
    if lo is not None and value < lo:
        raise UnsupportedValue(f"empty constraint range: {ops}")
    if "!=" in ops and value == ops["!="]:
        value += step
        if hi is not None and value > hi:
            value -= 2 * step
        if (lo is not None and value < lo) or (hi is not None and value > hi):
            raise UnsupportedValue(f"empty constraint range: {ops}")
    return value

def _variants(model: ModelType, jm: JsonModel, seen: frozenset[str],
              count: int) -> list[Jsonable]:
    """Distinct values matching a model, simplest first, at most count of them."""
    values: list[Jsonable]
    if model is None:
        values = [None]
    elif isinstance(model, bool):
        values = [False, True]
    elif isinstance(model, (int, float)):
        one: int|float = 1.0 if isinstance(model, float) else 1
        if model in (1, 1.0):
            values = [one * i for i in range(1, count + 1)]
        elif model in (0, 0.0):
            values = [one * i for i in range(count)]
        else:
            values = [one * 0]
            step = one
            while len(values) < count:
                values.append(step)
                values.append(-step)
                step += one
    elif model == "":
        values = [_ANY_CHAR * i for i in range(count)]
    elif isinstance(model, str) and not model.startswith(("/", "$")):
        values = [_simplest_string(model, jm, seen)]
    elif model == "$ANY":
        values = [{}, None, False, True, 0, "", []] + [_ANY_CHAR * i for i in range(1, count - 6)]
    elif isinstance(model, str) and model[1:] in PREDEFS:
        values = _variants(PREDEFS[model[1:]], jm, seen, count)
    elif isinstance(model, str) and model.startswith("$"):
        try:
            ja = jm.resolveRef(model, [])
        except (ModelError, AssertionError):
            values = []
        else:
            values = ([] if ja._url in seen
                      else _variants(ja._model, ja, seen | {ja._url}, count))
    elif isinstance(model, dict) and "|" in model:
        values, keys = [], set()
        for alt in model["|"]:
            if isinstance(alt, str) and alt.startswith("#"):
                continue
            for value in _variants(alt, jm, seen, count):
                key = _value_key(value)
                if key not in keys:
                    keys.add(key)
                    values.append(value)
    else:
        values = []
    return values[:count]

def _sized(target: ModelType, base: Jsonable, length: int, unique: bool,
           jm: JsonModel, seen: frozenset[str]) -> Jsonable:
    """Value of a given length for a resizable string or array model."""
    if jm._isRef(target):
        jm = jm.resolveRef(target, [])
        target = jm._model
    if jm._isPredef(target):
        target = PREDEFS[target[1:]]
    if isinstance(base, str):
        if target != "":
            raise UnsupportedValue(f"cannot resize string model: {target}")
        elif length <= len(_NAME_CHARS):
            return _NAME_CHARS[:length]
        else:
            return _ANY_CHAR * length
    items = [i for i in target if not (isinstance(i, str) and i.startswith("#"))]
    if not items:
        raise UnsupportedValue(f"cannot resize array model: {target}")
    models = [items[min(i, len(items) - 1)] for i in range(length)]
    if not unique or length <= 1:
        return [simplest(m, jm, seen) for m in models]
    values: list[Jsonable] = []
    keys: set[str] = set()
    for model in models:
        for value in _variants(model, jm, seen, length):
            key = _value_key(value)
            if key not in keys:
                keys.add(key)
                values.append(value)
                break
        else:
            raise UnsupportedValue(f"unique constraint needs {length} distinct values: {target}")
    return values

def _filled(model: ModelType, jm: JsonModel, seen: frozenset[str]) -> Jsonable:
    """Item value for an array, not an empty one when the model yields another."""
    for value in _variants(model, jm, seen, _ITEM_VARIANTS):
        if value or not isinstance(value, (str, list, dict)):
            return value
    return simplest(model, jm, seen)

def _holding(target: ModelArray, item: ModelType, ops: ModelObject,
             jm: JsonModel, seen: frozenset[str]) -> Jsonable|None:
    """Shortest non-empty array a model accepts, None when its constraints forbid any."""
    lo, hi = _bounds(ops, 1, 1)
    if hi is not None and hi < 1:
        return None
    try:
        length = int(_pick(lo, hi, ops, 1, 1))
    except UnsupportedValue:
        return None
    if "!" in ops:
        return _sized(target, [], length, True, jm, seen)
    else:
        return [_filled(item, jm, seen) for _ in range(length)]

def _kinds(jm: JsonModel, model: ModelType, seen: frozenset[str]) -> set[type]|None:
    """JSON types a model accepts, looking through references into unions, None if unknown."""
    if jm._isRef(model):
        node = jm.resolveRef(model, [])
        if node._url not in seen:
            model, jm, seen = node._model, node, seen | {node._url}
    op = next((o for o in ("|", "^") if isinstance(model, dict) and o in model), None)
    if op is None:
        kind = analyze.ultimate_type(jm, model)
        return None if kind is None else {kind}
    kinds: set[type] = set()
    for alt in model[op]:
        if isinstance(alt, str) and alt.startswith("#"):
            continue
        found = _kinds(jm, alt, seen)
        if found is None:
            return None
        kinds |= found
    return kinds

def _ultimate(jm: JsonModel, model: ModelType) -> set[type]|None:
    """JSON types a model accepts, None when any may be, an int always fitting a float."""
    try:
        kinds = _kinds(jm, model, frozenset())
    except ModelError:
        return None
    if kinds is not None and float in kinds:
        kinds.add(int)
    if kinds is not None and int in kinds and jm._loose_int:
        kinds.add(float)
    return kinds

def _mistyped(value: Jsonable, kinds: set[type]|None) -> bool:
    """Whether a value certainly cannot match a model accepting these types."""
    return kinds is not None and type(value) not in kinds

def _justified(utype: type|None) -> list[Jsonable]:
    """Type violations the oracle can justify first, so a marked value is a last resort."""
    return sorted(_TYPE_VIOLATIONS, key=lambda candidate: not _mistyped(candidate, utype))

def _checked(predef: str):
    """Existing format check for a predefined model: its backend implementation, else the fallback regex."""
    if predef in PYTHON_RUNTIME_PREDEFS:
        checker = getattr(support, PYTHON_RUNTIME_PREDEFS[predef])
        return lambda name: checker(name, "", None)
    elif predef in PREDEF_RE:
        _, pattern, options = PREDEF_RE[predef]
        flags = ((re.I if "i" in options else 0) | (re.S if "s" in options else 0))
        matcher = re.compile(pattern, flags)
        return lambda name: matcher.match(name) is not None
    else:
        return None

_PREDEF_NAMES = {name: check for name, check in
                 ((predef, _checked(predef)) for predef in STR_MODEL_PREDEFS
                  if not predef.startswith("$__"))
                 if check is not None}

def _matches(name: str, prop: str, jm: JsonModel|None = None) -> bool|None:
    """Whether a name matches an object model property key, None if undecided."""
    if prop == "" or prop in _ANY_NAME_PREDEFS:
        return True
    elif prop.startswith("#") or prop in _NO_NAME_PREDEFS:
        return False
    elif prop in _PREDEF_NAMES:
        return _PREDEF_NAMES[prop](name)
    elif prop.startswith("/"):
        if "/" not in prop[1:]:
            return None
        pattern, opts = prop[1:].rsplit("/", 1)
        if "X" in opts:
            return None
        source = f"(?{opts}){pattern}" if opts else pattern
        try:
            return re.compile(source).search(name) is not None
        except re.error:
            return None
    elif prop.startswith("$"):
        if jm is None or prop[1:] in PREDEFS:
            return None
        scope = jm.resolveRef(prop, [])
        if not isinstance(scope._model, str) or scope._model == prop:
            return None
        return _matches(name, scope._model, scope)
    else:
        return name == (prop[1:] if prop.startswith(("!", "?", "_")) else prop)

def _outranking(node: ModelObject, prop: str) -> list[str]:
    """Property keys the model applies before a catch-all or pattern key."""
    keys = [p for p in node if not p.startswith("#")]
    literals = [p for p in keys if p != "" and not p.startswith(("/", "$"))]
    predefs = [p for p in keys if p.startswith("$")]
    patterns = [p for p in keys if p.startswith("/")]
    if prop == "":
        return literals + predefs + patterns
    elif prop in patterns:
        return literals + predefs + patterns[:patterns.index(prop)]
    else:
        return []

def _names(prop: str, count: int, taken: set[str], outranking: list[str],
           jm: JsonModel|None = None) -> list[str]:
    """Distinct property names matching a catch-all or pattern property model."""
    try:
        seeds = list(_NAME_CHARS) if prop == "" else [_simplest_regex(prop)]
    except UnsupportedValue:
        return []
    names: list[str] = []
    for seed in seeds:
        for i in range(count + len(taken) + 1):
            name = seed + _ANY_CHAR * i
            if (name not in names and name not in taken
                    and _matches(name, prop, jm) is True
                    and not any(_matches(name, other, jm) is True for other in outranking)):
                names.append(name)
                if len(names) >= count:
                    return names
    return names

def _grown(target: ModelType, base: ModelObject, length: int,
           jm: JsonModel, seen: frozenset[str]) -> Jsonable:
    """Object of a given size, extended with optional or free properties."""
    if jm._isRef(target):
        jm = jm.resolveRef(target, [])
        target = jm._model
    if not is_a_simple_object(target):
        raise UnsupportedValue(f"cannot resize object model: {target}")
    elif len(base) > length:
        raise UnsupportedValue(f"cannot shrink object model: {target}")
    props = {p: m for p, m in target.items() if not p.startswith("#")}
    value = dict(base)
    for prop, submodel in props.items():
        if len(value) >= length:
            break
        elif prop.startswith("?") and prop[1:] not in value:
            value[prop[1:]] = simplest(submodel, jm, seen)
    for prop, submodel in props.items():
        if len(value) >= length:
            break
        elif prop == "" or prop.startswith("/"):
            for name in _names(prop, length - len(value), set(value),
                               _outranking(target, prop), jm):
                value[name] = simplest(submodel, jm, seen)
    if len(value) != length:
        raise UnsupportedValue(f"cannot reach {length} properties: {target}")
    else:
        return value

def _simplest_constrained(props: ModelObject, jm: JsonModel, seen: frozenset[str]) -> Jsonable:
    """Simplest value for a constraint model. To use only without comments"""
    target = props["@"]
    ops = {p: c for p, c in props.items() if p != "@"}
    if any(isinstance(c, bool) or not isinstance(c, (int, float))
           for p, c in ops.items() if p in _COMPARISONS):
        raise UnsupportedValue(f"unsupported comparison constraint: {ops}")
    unique = "!" in ops
    base = simplest(target, jm, seen)
    assert base is not None and not isinstance(base, bool), f"unsupported constrained model: {target}"
    assert not unique or isinstance(base, list), f"unique constraint on a non-array: {target}"
    if isinstance(base, (int, float)):
        is_float = isinstance(base, float)
        step: int|float = 1.0 if is_float else 1
        low = _numeric_low(jm.resolveRef(target, [])._model if jm._isRef(target) else target)
        lo, hi = _bounds(ops, step, low)
        value = _pick(lo, hi, ops, step, 0.0 if is_float else 0)
        return float(value) if is_float else int(value)
    lo, hi = _bounds(ops, 1, 0)
    if ((lo is None or len(base) >= lo) and (hi is None or len(base) <= hi)
            and not ("!=" in ops and len(base) == ops["!="])):
        return base
    length = int(_pick(lo, hi, ops, 1, 0))
    if isinstance(base, dict):
        return _grown(target, base, length, jm, seen)
    return _sized(target, base, length, unique, jm, seen)

def _simplest_union(alts: ModelArray, jm: JsonModel, seen: frozenset[str]) -> Jsonable:
    """Simplest value for the first alternative which yields one."""
    for alt in alts:
        if isinstance(alt, str) and alt.startswith("#"):
            continue
        else:
            try:
                return simplest(alt, jm, seen)
            except UnsupportedValue:
                pass
    raise UnsupportedValue(f"no alternative yields a value: {alts}")

def _simplest_operator(op: str, alts: ModelArray, jm: JsonModel,
                       seen: frozenset[str]) -> Jsonable:
    """Simplest value of the first alternative which yields one, for a xor one no other builds."""
    built: list[Jsonable] = []
    for alt in alts:
        if isinstance(alt, str) and alt.startswith("#"):
            continue
        try:
            built.append(simplest(alt, jm, seen))
        except UnsupportedValue:
            continue
    keys = [_value_key(value) for value in built]
    for value, key in zip(built, keys):
        if op != "^" or keys.count(key) == 1:
            return value
    if built:
        return built[0]
    raise UnsupportedValue(f"no alternative satisfies {op}: {alts}")

def _simplest_object(model: ModelObject, jm: JsonModel, seen: frozenset[str]) -> Jsonable:
    """Simplest value for a simple object model or a bare target model."""
    props = {p: m for p, m in model.items() if not p.startswith("#")}
    if "|" in props:
        return _simplest_union(props["|"], jm, seen)
    elif "^" in props:
        return _simplest_operator("^", props["^"], jm, seen)
    elif "&" in props:
        return _simplest_operator("&", props["&"], jm, seen)
    elif "@" in props:
        others = set(props) - {"@"}
        if not others:
            return simplest(props["@"], jm, seen)
        elif others <= _CONSTRAINTS:
            return _simplest_constrained(props, jm, seen)
    value: dict[str, Jsonable] = {}
    for prop, submodel in props.items():
        if prop == "" or prop.startswith(("?", "/", "$")):
            continue
        else:
            name = prop[1:] if prop.startswith(("!", "_")) else prop
            try:
                value[name] = simplest(submodel, jm, seen)
            except UnsupportedValue as e:
                raise type(e)(f"{prop}: {e}")
    return value

def _simplest_string(model: str, jm: JsonModel, seen: frozenset[str]) -> Jsonable:
    """Simplest value for a string model."""
    if model == "":
        return ""
    elif model.startswith(("_", "=")):
        return cst(model)
    elif model.startswith("/"):
        return _simplest_regex(model)
    elif model.startswith("$"):
        return _simplest_predef(model, jm, seen)
    else:
        return model

def simplest(model: ModelType, jm: JsonModel, seen: frozenset[str] = frozenset()) -> Jsonable:
    """Generate the simplest value matching a model."""
    match model:
        case None | bool() | int() | float():
            return _simplest_scalar(model)
        case str():
            return _simplest_string(model, jm, seen)
        case list():
            return _simplest_array(model, jm, seen)
        case dict():
            return _simplest_object(model, jm, seen)
        case _:
            assert False, f"unexpected model: {model}"

def _violation_value(op: str, bound: Jsonable, props: ModelObject, base: Jsonable,
                     jm: JsonModel, seen: frozenset[str]) -> Jsonable:
    """Candidate value just past a constraint, on its violating side."""
    target, ops = props["@"], {p: c for p, c in props.items() if p != "@"}
    if op == "!":
        assert bound is True, f"unsupported unique constraint: {bound}"
        lo, hi = _bounds(ops, 1, 0)
        lo = 2 if lo is None else max(lo, 2)
        return _sized(target, base, int(_pick(lo, hi, ops, 1, 0)), False, jm, seen)
    is_float = isinstance(base, float)
    table = _FLOAT_VIOLATIONS if is_float else _INT_VIOLATIONS
    if op not in table:
        raise UnsupportedValue(f"unsupported constraint: {op}")
    elif isinstance(base, dict):
        raise UnsupportedValue(f"cannot resize object model: {target}")
    candidate = table[op](bound)
    if not isinstance(candidate, float if is_float else int):
        raise UnsupportedValue(f"no value of the target type violates {op} {bound}")
    elif isinstance(base, (int, float)):
        return candidate
    elif candidate < 0:
        raise UnsupportedValue(f"no length violates {op} {bound}")
    else:
        return _sized(target, base, candidate, "!" in ops, jm, seen)

def _violations_constrained(props: ModelObject, jm: JsonModel,
                            seen: frozenset[str]) -> dict[str, Jsonable]:
    """One value per constraint, meant to break only that one."""
    target = props["@"]
    ops = {p: c for p, c in props.items() if p != "@"}
    if any(isinstance(c, str) for p, c in ops.items() if p in _COMPARISONS):
        raise UnsupportedValue(f"unsupported string comparison constraint: {ops}")
    base = simplest(target, jm, seen)
    assert isinstance(base, (int, float, str, list, dict)) and not isinstance(base, bool), \
        f"unsupported constrained model: {target}"
    assert "!" not in ops or isinstance(base, list), f"unique constraint on a non-array: {target}"
    values: dict[str, Jsonable] = {}
    for op, bound in ops.items():
        try:
            values[op] = _violation_value(op, bound, props, base, jm, seen)
        except UnsupportedValue:
            values[op] = base
    return values

def _bound_value(table: dict, op: str, bound: Jsonable, props: ModelObject,
                 base: Jsonable, jm: JsonModel, seen: frozenset[str]) -> Jsonable:
    """Candidate value on the last step a constraint still accepts."""
    target, ops = props["@"], {p: c for p, c in props.items() if p != "@"}
    is_float = isinstance(base, float)
    if op not in table:
        raise UnsupportedValue(f"no exact bound for constraint: {op}")
    candidate = table[op](bound)
    if not isinstance(candidate, float if is_float else int):
        raise UnsupportedValue(f"no value of the target type reaches {op} {bound}")
    elif isinstance(base, (int, float)):
        return candidate
    elif candidate < 0:
        raise UnsupportedValue(f"no length reaches {op} {bound}")
    if isinstance(base, dict):
        return _grown(target, base, candidate, jm, seen)
    else:
        return _sized(target, base, candidate, "!" in ops, jm, seen)

def _bound_candidates(op: str, bound: Jsonable, props: ModelObject, base: Jsonable,
                      jm: JsonModel, seen: frozenset[str]):
    """Values which may sit on a constraint bound, best first."""
    tables = [_FLOAT_BOUNDS if isinstance(base, float) else _INT_BOUNDS]
    if op == "!=" and not isinstance(base, float):
        tables.append(_INT_MIRRORS)
    for table in tables:
        try:
            yield _bound_value(table, op, bound, props, base, jm, seen)
        except UnsupportedValue:
            pass

def _bounds_constrained(props: ModelObject, jm: JsonModel,
                        seen: frozenset[str]) -> dict[str, Jsonable]:
    """One value per constraint, each on the last step it still accepts."""
    target = props["@"]
    ops = {p: c for p, c in props.items() if p != "@"}
    if any(isinstance(c, bool) or not isinstance(c, (int, float))
           for p, c in ops.items() if p in _COMPARISONS):
        raise UnsupportedValue(f"unsupported comparison constraint: {ops}")
    base = simplest(target, jm, seen)
    values: dict[str, Jsonable] = {}
    for op, bound in ops.items():
        for value in _bound_candidates(op, bound, props, base, jm, seen):
            values[op] = value
            break
    if not values:
        raise UnsupportedValue(
            f"no bound reached for {', '.join(ops)} in model: {_brief(target)}")
    else:
        return values

def _mandatory(node: ModelObject) -> list[tuple[str, str]]:
    """Model key and value name of each mandatory property of an object model."""
    props = []
    for prop in node:
        if prop == "" or prop.startswith(("#", "?", "/", "$")):
            continue
        props.append((prop, prop[1:] if prop.startswith(("!", "_")) else prop))
    return props

def _optional_props(node: ModelObject, jm: JsonModel,
                    seen: frozenset[str]) -> list[tuple[str, str, ModelType]]:
    """Model key, value name and model of each optional property."""
    named = {p[1:] if p.startswith(("!", "?", "_")) else p
             for p in node if p and not p.startswith(("/", "$", "#"))}
    props: list[tuple[str, str, ModelType]] = []
    for prop, sub in node.items():
        if prop.startswith("#"):
            continue
        elif prop.startswith("?"):
            props.append((prop, prop[1:], sub))
        elif prop == "" or prop.startswith("/"):
            props.extend((prop, name, sub)
                         for name in _names(prop, 1, named, _outranking(node, prop), jm))
        elif prop.startswith("$"):
            try:
                name = simplest(prop, jm, seen)
            except UnsupportedValue:
                continue
            if isinstance(name, str) and name not in named:
                props.append((prop, name, sub))
    return props

def _closed(node: ModelObject, jm: JsonModel) -> bool:
    """Whether an object model rejects properties it does not describe."""
    if "" not in node:
        return True
    try:
        simplest(node[""], jm)
        return False
    except UnsupportedValue:
        return True

def _object_sites(sites: list):
    """Sites which target a plain object model."""
    for mpath, vpath, frames, props, disjunction, guarded in sites:
        node = props["@"]
        if (not set(props) - {"@"} and isinstance(node, dict)
                and is_a_simple_object(node)):
            yield mpath, vpath, frames, node, disjunction, guarded

def _array_sites(sites: list):
    """Sites which target an array model of one item model, with that model."""
    for mpath, vpath, frames, props, disjunction, guarded in sites:
        node = props["@"]
        if set(props) - {"@"} or not isinstance(node, list):
            continue
        models = [m for m in node if not (isinstance(m, str) and m.startswith("#"))]
        if len(models) == 1:
            yield mpath, vpath, frames, node, models[0], disjunction, guarded

def _alternatives(sites: list):
    """Sites which target a union model."""
    for mpath, vpath, frames, props, disjunction, guarded in sites:
        node = props["@"]
        if set(props) - {"@"} or not isinstance(node, dict):
            continue
        op = "|" if "|" in node else "^" if "^" in node else None
        if op is not None:
            yield mpath, vpath, frames, node, op, disjunction, guarded

def _overlapping(alts: ModelArray, jm: JsonModel,
                 seen: frozenset[str]) -> list[Jsonable]:
    """Value two alternatives of a xor build, which it therefore refuses."""
    models: dict[str, ModelType] = {}
    for alt in alts:
        if not (isinstance(alt, str) and alt.startswith("#")):
            models.setdefault(_value_key(alt), alt)
    built: dict[str, Jsonable] = {}
    for alt in models.values():
        try:
            value = simplest(alt, jm, seen)
        except UnsupportedValue:
            continue
        dumped = _value_key(value)
        if dumped in built:
            return [built[dumped]]
        built[dumped] = value
    return []

def _exclusive_sites(sites: list):
    """Sites which target an exclusive union model."""
    for mpath, vpath, frames, props, disjunction, guarded in sites:
        node = props["@"]
        if set(props) - {"@"} or not isinstance(node, dict):
            continue
        if "^" in node:
            yield mpath, vpath, frames, node, disjunction, guarded

def _mpath(path: list) -> str:
    """Readable model path, written in JSON Model syntax."""
    steps: list[str] = []
    index = 0
    while index < len(path):
        step = path[index]
        follow = path[index + 1] if index + 1 < len(path) else None
        index += 1
        if isinstance(step, int) and not isinstance(step, bool):
            steps.append(f"[{step}]")
            continue
        name = str(step)
        if name == "$" and isinstance(follow, str):
            steps.append(f".${follow}")
            index += 1
        elif name in _QUOTED_OPS or not _MODEL_NAME_RE.match(name):
            steps.append(f".'{name}'")
        else:
            steps.append(f".{name}")
    text = "".join(steps)
    return "." + text if not text or text[0] == "[" else text

def _replaced(doc: Jsonable, path: list, value: Jsonable) -> Jsonable:
    """Copy of a document with one position set to a value."""
    result = copy.deepcopy(doc)
    node = result
    try:
        for step in path[:-1]:
            node = node[step]
        node[path[-1]] = value
    except (KeyError, IndexError, TypeError) as e:
        raise UnsupportedValue(f"cannot set {support._path(path)} in document: {e}")
    return result

def _sites(model: ModelType, mpath: list, vpath: list, frames: list,
           jm: JsonModel, seen: frozenset[str], notes: list[str]|None = None,
           disjunction: tuple[list, ModelObject]|None = None,
           guarded: tuple = (False, ())):
    """Violation sites, as model path, value path, branch frames, properties and disjunction."""
    if isinstance(model, str):
        name = model[1:]
        if model.startswith("$") and name in jm._defs._syms and name not in seen:
            yield from _sites(jm._defs._syms[name]._model, mpath + ["$", name], vpath,
                              frames, jm, seen | {name}, notes, disjunction, guarded)
        elif model != "$ANY" and (not model.startswith("$") or name in PREDEFS):
            yield mpath, vpath, frames, {"@": model}, disjunction, guarded
        elif model == "$ANY" and notes is not None:
            notes.append(f"{_mpath(mpath)} invalid: $ANY accepts every value")
    elif isinstance(model, list):
        yield mpath, vpath, frames, {"@": model}, disjunction, guarded
        items = [(i, m) for i, m in enumerate(model)
                 if not (isinstance(m, str) and m.startswith("#"))]
        if len(items) > 1:
            for n, (i, item) in enumerate(items):
                yield from _sites(item, mpath + [i], vpath + [n], frames, jm, seen,
                                  notes, disjunction, guarded)
        elif items:
            i, item = items[0]
            held = {"@": model, ">=": 1, **_guarding(guarded, vpath)}
            yield from _sites(item, mpath + [i], vpath + [0],
                              frames + [(vpath, held)], jm, seen,
                              notes, disjunction, guarded)
    elif isinstance(model, dict):
        props = {p: m for p, m in model.items() if not p.startswith("#")}
        others = set(props) - {"@"}
        if "@" in props and others <= _CONSTRAINTS:
            if others:
                yield mpath, vpath, frames, props, disjunction, guarded
            yield from _sites(props["@"], mpath + ["@"], vpath, frames, jm, seen,
                              notes, disjunction,
                              (guarded[0],
                               guarded[1] + ((vpath, {p: props[p] for p in others}),))
                              if others else guarded)
        elif "|" in props or "^" in props or "&" in props:
            op = "|" if "|" in props else "^" if "^" in props else "&"
            yield mpath, vpath, frames, {"@": model}, disjunction, guarded
            inner = (disjunction if disjunction is not None or op == "&"
                     else (vpath, props))
            for index, alt in enumerate(props[op]):
                if isinstance(alt, str) and alt.startswith("#"):
                    continue
                yield from _sites(alt, mpath + [op, index], vpath,
                                  frames + [(vpath, alt)], jm, seen, notes, inner,
                                  (guarded[0] or op != "|", guarded[1]))
        elif is_a_simple_object(props):
            yield mpath, vpath, frames, {"@": model}, disjunction, guarded
            named = {p[1:] if p.startswith(("!", "?", "_")) else p
                     for p in props if p and not p.startswith(("/", "$"))}
            for prop, sub in props.items():
                if prop == "" or prop.startswith("$"):
                    continue
                elif prop.startswith("/"):
                    found = _names(prop, 1, named, _outranking(props, prop), jm)
                    if not found:
                        if notes is not None:
                            notes.append(f"{_mpath(mpath + [prop])} invalid: no free property name for {prop}")
                        continue
                    name = found[0]
                    inner = frames + [(vpath + [name], sub)]
                else:
                    name = prop[1:] if prop.startswith(("!", "?", "_")) else prop
                    inner = (frames + [(vpath + [name], sub)] if prop.startswith("?")
                             else frames)
                yield from _sites(sub, mpath + [prop], vpath + [name], inner, jm, seen,
                                  notes, disjunction, guarded)
    else:
        yield mpath, vpath, frames, {"@": model}, disjunction, guarded

def _document(sub: Jsonable, vpath: list, frames: list, doc: Jsonable,
              jm: JsonModel, seen: frozenset[str]) -> Jsonable:
    """Whole document holding a violating value at one position."""
    value, path = sub, vpath
    for vp, branch in reversed(frames):
        if path != vp:
            value = _replaced(simplest(branch, jm, seen), path[len(vp):], value)
        path = vp
    if not path:
        return value
    elif doc is None:
        raise UnsupportedValue("no document to alter")
    else:
        return _replaced(doc, path, value)

def _violations(model: ModelType, jm: JsonModel,
                seen: frozenset[str] = frozenset(),
                marks: set[str]|None = None,
                valid: frozenset[str] = frozenset()
                ) -> tuple[dict[str, Jsonable], list[str], list[str], list[str]]:
    """Generate a value breaking each constraint, and which sites were skipped, repeated or lost."""
    skipped: list[str] = []
    doubled: list[str] = []
    failed: list[str] = []
    sites = list(_sites(model, [], [], [], jm, frozenset(), skipped))
    if not sites:
        if skipped:
            raise Vacuous(f"every value matches the model: {_brief(model)}")
        raise UnsupportedValue(f"cannot enter model: {_brief(model)}")
    values: dict[str, Jsonable] = {}
    taken: set[str] = set()
    reasons: list[str] = []
    doc = None

    def skip(note: str):
        """Record a case which cannot exist for this model."""
        reasons.append(note)
        if note not in skipped:
            skipped.append(note)

    def repeats(key: str, value: Jsonable) -> bool:
        """Whether a violation repeats a value already generated as valid."""
        if _value_key(value) not in valid:
            return False
        skip(f"{key}: valid for the model")
        return True

    def doubles(key: str) -> None:
        """Record a site whose value another site already produced."""
        if key not in doubled:
            doubled.append(key)

    def failure(key: str, error: object) -> None:
        """Record a site the generator could not build."""
        note = f"{key}: {error}"
        reasons.append(note)
        if note not in failed:
            failed.append(note)

    def proposed(key: str) -> None:
        """Mark a violation the generator proposes, which only the checker settles."""
        if marks is not None:
            marks.add(key)

    if any(f[0][0] if f else v for _, v, f, _, _, _ in sites):
        try:
            doc = simplest(model, jm, seen)
        except UnsupportedValue as e:
            failure("violation values", f"no document to alter: {e}")
    for mpath, vpath, frames, props, disjunction, guarded in sites:
        ops = set(props) - {"@"}
        if not ops or all(_mpath(mpath + [op]) in values for op in ops):
            continue
        try:
            subs = _violations_constrained(props, jm, seen)
        except UnsupportedValue as e:
            failure(_mpath(mpath), e)
            continue
        for op, sub in subs.items():
            key = _mpath(mpath + [op])
            if key in values:
                continue
            try:
                value = _document(sub, vpath, frames, doc, jm, seen)
            except UnsupportedValue as e:
                failure(key, e)
                continue
            dumped = _value_key(value)
            if dumped in taken:
                doubles(key)
                continue
            elif repeats(key, value):
                continue
            proposed(key)
            taken.add(dumped)
            values[key] = value
    for mpath, vpath, frames, props, disjunction, guarded in sites:
        key = f"{_mpath(mpath)} invalid"
        if not mpath or set(props) - {"@"} or key in values:
            continue
        node = (disjunction[1] if disjunction is not None and vpath == disjunction[0]
                else props["@"])
        for candidate in _justified(_ultimate(jm, node)):
            try:
                value = _document(copy.deepcopy(candidate), vpath, frames, doc, jm, seen)
            except UnsupportedValue as e:
                failure(key, e)
                break
            if _value_key(value) in taken:
                doubles(key)
                break
            elif repeats(key, value):
                break
            proposed(key)
            values[key] = value
            taken.add(_value_key(value))
            break
        else:
            skip(f"{key}: no type breaks the model here")
    for mpath, vpath, frames, props, disjunction, guarded in sites:
        key = f"{_mpath(mpath)} bad"
        if set(props) - {"@"} or key in values:
            continue
        target = props["@"]
        if not isinstance(target, str) or target not in _PREDEF_VIOLATIONS:
            continue
        try:
            value = _document(copy.deepcopy(_PREDEF_VIOLATIONS[target]),
                              vpath, frames, doc, jm, seen)
        except UnsupportedValue as e:
            failure(key, e)
            continue
        if _value_key(value) in taken:
            doubles(key)
            continue
        elif repeats(key, value):
            continue
        proposed(key)
        taken.add(_value_key(value))
        values[key] = value
    for mpath, vpath, frames, node, disjunction, guarded in _object_sites(sites):
        try:
            built = simplest(node, jm, seen)
        except UnsupportedValue as e:
            failure(f"{_mpath(mpath)} missing", f"no object to shrink: {e}")
            continue
        if not isinstance(built, dict):
            continue
        for prop, name in _mandatory(node):
            key = f"{_mpath(mpath + [prop])} missing"
            if key in values or name not in built:
                continue
            sub = {p: v for p, v in built.items() if p != name}
            try:
                value = _document(sub, vpath, frames, doc, jm, seen)
            except UnsupportedValue as e:
                failure(key, e)
                break
            if _value_key(value) in taken:
                doubles(key)
                continue
            elif repeats(key, value):
                continue
            proposed(key)
            taken.add(_value_key(value))
            values[key] = value
    for mpath, vpath, frames, node, disjunction, guarded in _object_sites(sites):
        if not _closed(node, jm):
            skip(f"{_mpath(mpath)} extra: object is open")
            continue
        try:
            built = simplest(node, jm, seen)
        except UnsupportedValue as e:
            failure(f"{_mpath(mpath)} extra", f"no object to extend: {e}")
            continue
        if not isinstance(built, dict):
            continue
        for name in _EXTRA_NAMES:
            key = f"{_mpath(mpath + [name])} extra"
            if name in built or key in values:
                continue
            sub = {**built, name: None}
            try:
                value = _document(sub, vpath, frames, doc, jm, seen)
            except UnsupportedValue as e:
                failure(key, e)
                break
            if _value_key(value) in taken:
                doubles(key)
                break
            elif repeats(key, value):
                break
            proposed(key)
            values[key] = value
            taken.add(_value_key(value))
            break
        else:
            skip(f"{_mpath(mpath)} extra: every extra property is valid")
    for mpath, vpath, frames, node, disjunction, guarded in _exclusive_sites(sites):
        key = f"{_mpath(mpath + ['^'])} overlap"
        if key in values:
            continue
        found = _overlapping(node["^"], jm, seen)
        if not found:
            continue
        shared = found[0]
        try:
            value = _document(shared, vpath, frames, doc, jm, seen)
        except UnsupportedValue as e:
            failure(key, e)
            continue
        dumped = _value_key(value)
        if dumped in taken:
            doubles(key)
            continue
        elif repeats(key, value):
            continue
        proposed(key)
        taken.add(dumped)
        values[key] = value
    for candidate in _ROOT_TYPES:
        dumped = _value_key(candidate)
        key = _rooted(candidate)
        if dumped in taken:
            doubles(key)
            continue
        proposed(key)
        values[key] = copy.deepcopy(candidate)
        taken.add(dumped)
    if not values:
        if not reasons:
            reasons.append("no violation site could be used")
        note = f"no constraint could be violated: {_joined(reasons)}"
        raise UnsupportedValue(note) if failed else Vacuous(note)
    else:
        covered = values.keys() | {n.partition(": ")[0] for n in skipped} | set(doubled)
        return (values, skipped, doubled,
                [n for n in failed if n.partition(": ")[0] not in covered])

def bounds(model: ModelType, jm: JsonModel, seen: frozenset[str] = frozenset(),
           marks: set[str]|None = None) -> dict[str, Jsonable]:
    """Generate a value on the bound of each constraint of a model."""
    marks = set() if marks is None else marks
    notes: list[str] = []
    sites = list(_sites(model, [], [], [], jm, frozenset(), notes))
    if not sites and not notes:
        raise UnsupportedValue(f"cannot enter model: {_brief(model)}")
    values: dict[str, Jsonable] = {}
    reasons: list[str] = []
    doc = None
    if any(f[0][0] if f else v for _, v, f, _, _, _ in sites):
        try:
            doc = simplest(model, jm, seen)
        except UnsupportedValue as e:
            reasons.append(f"no document to alter: {e}")
    for mpath, vpath, frames, props, disjunction, guarded in sites:
        ops = set(props) - {"@"}
        if not ops or all(_mpath(mpath + [op]) in values for op in ops):
            continue
        try:
            subs = _bounds_constrained(props, jm, seen)
        except UnsupportedValue as e:
            reasons.append(str(e))
            continue
        for op, sub in subs.items():
            key = _mpath(mpath + [op])
            if key in values:
                continue
            try:
                value = _document(sub, vpath, frames, doc, jm, seen)
            except UnsupportedValue as e:
                reasons.append(f"{key}: {e}")
                continue
            values[key] = value
            marks.add(key)
    if not values:
        if not reasons:
            raise Vacuous("no constraint bound: no constraint in model")
        raise UnsupportedValue(f"no constraint bound: {_joined(reasons)}")
    else:
        return values

def optionals(model: ModelType, jm: JsonModel, seen: frozenset[str] = frozenset(),
              marks: set[str]|None = None
              ) -> tuple[dict[str, Jsonable], list[str], list[str]]:
    """Generate a valid value per optional property, why the others were skipped or repeated."""
    marks = set() if marks is None else marks
    sites = list(_sites(model, [], [], [], jm, frozenset()))
    values: dict[str, Jsonable] = {}
    reasons: list[str] = []
    doubled: list[str] = []
    doc = None
    try:
        doc = simplest(model, jm, seen)
    except Vacuous:
        raise
    except UnsupportedValue as e:
        reasons.append(f"optional values: no document to alter: {e}")
    taken = set() if doc is None else {_value_key(doc)}
    for mpath, vpath, frames, node, disjunction, guarded in _object_sites(sites):
        props = _optional_props(node, jm, seen)
        if not props:
            continue
        try:
            built = simplest(node, jm, seen)
        except UnsupportedValue as e:
            reasons.append(f"{_mpath(mpath)} optional: no object to extend: {e}")
            continue
        if not isinstance(built, dict):
            continue
        for prop, name, submodel in props:
            key = f"{_mpath(mpath + [prop])} present"
            if key in values or name in built:
                continue
            try:
                sub = {**built, name: simplest(submodel, jm, seen)}
                value = _document(sub, vpath, frames, doc, jm, seen)
            except Vacuous:
                continue
            except UnsupportedValue as e:
                reasons.append(f"{key}: {e}")
                continue
            dumped = _value_key(value)
            if dumped in taken:
                doubled.append(key)
                continue
            marks.add(key)
            values[key] = value
            taken.add(dumped)
    if not values and not reasons and not doubled:
        raise Vacuous(f"no optional property in model: {_brief(model)}")
    return values, reasons, doubled

def branches(model: ModelType, jm: JsonModel, seen: frozenset[str] = frozenset(),
             marks: set[str]|None = None
             ) -> tuple[dict[str, Jsonable], list[str], list[str]]:
    """Generate a valid value per union alternative, why the others were skipped or repeated."""
    marks = set() if marks is None else marks
    sites = list(_sites(model, [], [], [], jm, frozenset()))
    values: dict[str, Jsonable] = {}
    reasons: list[str] = []
    doubled: list[str] = []
    doc = None
    try:
        doc = simplest(model, jm, seen)
    except Vacuous:
        raise
    except UnsupportedValue as e:
        reasons.append(f"branch values: no document to alter: {e}")
    taken = set() if doc is None else {_value_key(doc)}
    for mpath, vpath, frames, node, op, disjunction, guarded in _alternatives(sites):
        for index, alt in enumerate(node[op]):
            if isinstance(alt, str) and alt.startswith("#"):
                continue
            key = f"{_mpath(mpath + [op, index])} branch"
            if key in values:
                continue
            try:
                sub = simplest(alt, jm, seen)
                value = _document(sub, vpath, frames, doc, jm, seen)
            except Vacuous:
                continue
            except UnsupportedValue as e:
                reasons.append(f"{key}: {e}")
                continue
            dumped = _value_key(value)
            if dumped in taken:
                doubled.append(key)
                continue
            marks.add(key)
            values[key] = value
            taken.add(dumped)
    if not values and not reasons and not doubled:
        raise Vacuous(f"no union alternative in model: {_brief(model)}")
    return values, reasons, doubled

def _guarding(guarded: tuple, vpath: list) -> ModelObject:
    """Numeric constraints standing above a site which apply to its own value."""
    return {p: c for vp, ops in guarded[1] if vp == vpath for p, c in ops.items()
            if p == "!" or (not isinstance(c, bool) and isinstance(c, (int, float)))}

def items(model: ModelType, jm: JsonModel, seen: frozenset[str] = frozenset(),
          marks: set[str]|None = None
          ) -> tuple[dict[str, Jsonable], list[str], list[str]]:
    """Generate a valid value per array model, holding an item, why the others were skipped."""
    marks = set() if marks is None else marks
    sites = list(_sites(model, [], [], [], jm, frozenset()))
    values: dict[str, Jsonable] = {}
    reasons: list[str] = []
    doubled: list[str] = []
    doc = None
    try:
        doc = simplest(model, jm, seen)
    except Vacuous:
        raise
    except UnsupportedValue as e:
        reasons.append(f"item values: no document to alter: {e}")
    taken = set() if doc is None else {_value_key(doc)}
    for mpath, vpath, frames, node, item, disjunction, guarded in _array_sites(sites):
        key = f"{_mpath(mpath)} item"
        if key in values:
            continue
        try:
            sub = _holding(node, item, _guarding(guarded, vpath), jm, seen)
            if sub is None:
                continue
            value = _document(sub, vpath, frames, doc, jm, seen)
        except Vacuous:
            continue
        except UnsupportedValue as e:
            reasons.append(f"{key}: {e}")
            continue
        dumped = _value_key(value)
        if dumped in taken:
            doubled.append(key)
            continue
        marks.add(key)
        values[key] = value
        taken.add(dumped)
    if not values and not reasons and not doubled:
        raise Vacuous(f"no array to hold an item in model: {_brief(model)}")
    return values, reasons, doubled

_EXPLANATIONS = (" root invalid", " root", " bound", " present", " branch", " item",
                 " invalid", " missing", " extra", " bad", " overlap")

_ROOT_INVALID = " root invalid"
_ROOT_GUESS = f"# .{_ROOT_INVALID}"

def _rooted(value: Jsonable) -> str:
    """Key of a root type violation, naming the value it is about."""
    shown = f"'{value}'" if isinstance(value, str) else json.dumps(value, sort_keys=True)
    return f".{shown}{_ROOT_INVALID}"

def _shown(key: str) -> str:
    """Key of a comment, without the root value which the test vector shows anyway."""
    return f".{_ROOT_INVALID}" if key.endswith(_ROOT_INVALID) else key

def _label(key: str, marks: set[str], suffix: str = "") -> str:
    """Comment introducing a test vector, marked when the compiler was not asked."""
    head = _shown(key)
    return f"# {head}{suffix} AGREES" if key in marks else f"# {head}{suffix}"

def _note(reason: str, warn: str) -> tuple[str, list]:
    """Path and comment about a test vector which could not be generated."""
    head, sep, detail = reason.partition(": ")
    return _path(head), [f"# {head} {warn}{sep}{detail}"]

def _path(key: str) -> str:
    """Model path a comment is about, without the explanation which follows it."""
    key = _shown(key)
    for word in _EXPLANATIONS:
        if key.endswith(word):
            return key[:-len(word)]
    return key

def _ordered(entries: list[tuple[int, str, list]]) -> list:
    """Test vectors valid before invalid, sorted by model path inside each group."""
    def rank(entry: tuple[int, str, list]) -> tuple:
        group, path, _ = entry
        return group, tuple((1, int(s), "") if s.isdigit() else (0, 0, s)
                            for s in re.split(r"(\d+)", path))
    return [item for *_, entry in sorted(entries, key=rank) for item in entry]

_AGREES = " AGREES"
_SIMPLEST = "# . simplest"
_REPEATED = "DUPLICATE BAD"
_PASSED = "BAD PASS"
_FAILED = "BAD FAIL"
_NO_BASE = "no value the compiler accepts, every vector below builds on this one"

def _checker(jm: JsonModel) -> EntryCheckFun|None:
    """Checker of the whole model, None when it cannot be built."""
    from .script import model_checker
    try:
        return model_checker(jm)
    except Exception:
        return None

def _recheck(entries: list[tuple[int, str, list]], jm: JsonModel) -> None:
    """Settle every mark against one checker of the whole model, null where it disagrees."""
    judged = [entry for *_, entry in entries
              if len(entry) == 2 and isinstance(entry[0], str)]
    if not judged:
        return
    def cleared(entry: list) -> None:
        """Drop the mark of a vector which is not waiting on the compiler."""
        if entry[0].endswith(_AGREES):
            entry[0] = entry[0][:-len(_AGREES)]
    def remark(entry: list, verdict: str) -> None:
        cleared(entry)
        entry[0] += " " + verdict
    def commented(entry: list, verdict: str) -> None:
        """Shrink a vector which adds nothing to the comment which says why."""
        remark(entry, verdict)
        del entry[1]
    check = _checker(jm)
    def verdict(value: Jsonable) -> bool|None:
        """What the checker says of a value, None without one."""
        if check is None:
            return None
        try:
            return check(value, "", None)
        except RecursionError:
            return None
    results = [verdict(entry[1][1]) for entry in judged]
    def settled(index: int, entry: list) -> bool:
        """Whether the file may state the verdict of a vector as it stands."""
        if entry[0].endswith(_AGREES):
            return False
        return results[index] is None or results[index] == entry[1][0]
    stated = {_value_key(entry[1][1])
              for index, entry in enumerate(judged) if settled(index, entry)}
    refused = False
    dropped: set[int] = set()
    for index, entry in enumerate(judged):
        expect, value = entry[1]
        result = results[index]
        if entry[0].startswith(_ROOT_GUESS) and result is not False:
            dropped.add(id(entry))
            continue
        if result is False and entry[0].startswith(_SIMPLEST):
            refused = True
        dumped = _value_key(value)
        marked = entry[0].endswith(_AGREES)
        if marked and dumped in stated:
            commented(entry, _REPEATED)
            continue
        if result is not None and result != expect:
            remark(entry, _FAILED if expect else _PASSED)
            entry[1][0] = None
        elif marked and result is None:
            remark(entry, "BAD")
            entry[1][0] = None
        else:
            cleared(entry)
            entry[1][0] = expect
            stated.add(dumped)
    entries[:] = [e for e in entries if id(e[2]) not in dropped]
    if refused:
        entries.append((0, ".", _note(f"base values: {_NO_BASE}", "FAILED")[1]))

def vectors(model: ModelType, resolver: Resolver|None = None, url: str = "",
            extend: bool = False) -> list:
    """Test vectors for a model, sorted by model path, valid values before violations."""
    entries: list[tuple[int, str, list]] = []
    reasons: list[str] = []
    taken: set[str] = set()
    from .script import model_from_json
    try:
        jm = model_from_json(model, murl=url, resolver=resolver, extend=extend)
    except (ModelError, AssertionError, KeyError) as e:
        raise UnsupportedValue(f"no test vector: unsupported model: {e}")
    compiled = jm._model
    try:
        valid = simplest(compiled, jm)
        entries.append((0, ".", ["# . simplest", [True, valid]]))
        taken.add(_value_key(valid))
    except Vacuous as e:
        reasons.append(str(e))
        entries.append((0, ".", _note(f". simplest: {e}", "SKIPPED")[1]))
    except UnsupportedValue as e:
        reasons.append(str(e))
        entries.append((0, ".", _note(f". simplest: {e}", "FAILED")[1]))
    try:
        marks: set[str] = set()
        found = bounds(compiled, jm, marks=marks)
        for key, value in found.items():
            dumped = _value_key(value)
            if dumped in taken:
                entries.append((0, *_note(f"{key} bound", "DUPLICATE")))
                continue
            taken.add(dumped)
            entries.append((0, _path(key), [_label(key, marks, " bound"), [True, value]]))
    except Vacuous as e:
        reasons.append(str(e))
    except UnsupportedValue as e:
        reasons.append(str(e))
        entries.append((0, ".", _note(f"bound values: {e}", "FAILED")[1]))
    for step, generate in (("optional", optionals), ("branch", branches), ("item", items)):
        try:
            step_marks: set[str] = set()
            found, skipped, doubled = generate(compiled, jm, marks=step_marks)
            for key, value in found.items():
                dumped = _value_key(value)
                if dumped in taken:
                    entries.append((0, *_note(key, "DUPLICATE")))
                    continue
                taken.add(dumped)
                entries.append((0, _path(key), [_label(key, step_marks), [True, value]]))
            for reason in skipped:
                entries.append((0, *_note(reason, "FAILED")))
            for reason in doubled:
                entries.append((0, *_note(reason, "DUPLICATE")))
        except Vacuous as e:
            reasons.append(str(e))
        except UnsupportedValue as e:
            reasons.append(str(e))
            entries.append((0, ".", _note(f"{step} values: {e}", "FAILED")[1]))
    try:
        broken_marks: set[str] = set()
        broken, skipped, doubled, lost = _violations(compiled, jm, marks=broken_marks,
                                                     valid=frozenset(taken))
        for key, value in broken.items():
            entries.append((1, _path(key), [_label(key, broken_marks), [False, value]]))
        for reason in skipped:
            entries.append((1, *_note(reason, "SKIPPED")))
        for reason in doubled:
            entries.append((1, *_note(reason, "DUPLICATE")))
        for reason in lost:
            entries.append((1, *_note(reason, "FAILED")))
    except Vacuous as e:
        reasons.append(str(e))
        entries.append((1, ".", _note(f"violation values: {e}", "SKIPPED")[1]))
    except UnsupportedValue as e:
        reasons.append(str(e))
        entries.append((1, ".", _note(f"violation values: {e}", "FAILED")[1]))
    if not any(len(entry) > 1 for *_, entry in entries):
        raise UnsupportedValue(f"no test vector: {_joined(reasons)}")
    _recheck(entries, jm)
    return _ordered(entries)
