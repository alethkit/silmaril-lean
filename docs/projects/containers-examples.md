# Container examples

**Experimental API.** The `Containers` region (`Silmaril/Containers/…`) may change; the design is
in [Containers](containers.md).

Six worked examples: a real static ELF in an OCI image, and five small model programs. Each is a
registered problem of the group `containers.examples`, so its verdict comes from the registry.

| Example | Kind | Runs as | Verified | Verdict |
| --- | --- | --- | --- | --- |
| No-op | real | OCI image → static x86-64 ELF → LPS | no undefined behaviour, exit 0, no events | holds |
| Crash | model | killed by `SIGSEGV` | no undefined behaviour, partial correctness | holds |
| Crash | model | killed by `SIGSEGV` | no undefined behaviour, exits | fails: it never exits |
| Thread creation | model | `clone` with `pthread_create`'s flags | no undefined behaviour | fails: undefined under the sequential policy |
| HTTP/1.1 server | model | TCP on 8080, one fixed response | TCP only, only `HTTP/1.1 200 OK`, only declared ports | holds |
| vsock compute | model | vsock port 5005, answers reversed | vsock only, exits 0 after answering | holds |

## Try it

```
lake build Silmaril.Containers.Noop.Thms Silmaril.Containers.Fixtures.Thms \
  Silmaril.Containers.Mini.Thms Silmaril.Containers.Http.Thms
lake env lean --run examples/containers/Examples.lean           # every example
lake env lean --run examples/containers/Examples.lean http      # one: noop, crash, thread, http, vsock
examples/containers/noop-oci/docker-test.sh                     # the real image under Docker
```

`Examples.lean` prints each example: its image (with digests), runtime, machine, clone policy,
profile, specification, the run the theorem proves and the theorems. It runs the model examples on
a sample input and reads the real image from `examples/containers/noop-oci/layout`, with the
reader the proof uses. For example:

```
HTTP/1.1 server on 8080/tcp  [model]  (containers.examples.http)
  profile:   tcpOnly
  spec:      no undefined behaviour; TCP only; every response is `HTTP/1.1 200 OK` …
  executed now:  socket(inet4); bind(port 8080); listen; accept; recv "GET / HTTP/1.1"… (35 bytes);
                 send "HTTP/1.1 200 OK"… (40 bytes); close; (waits for the next connection)
  theorems:  Silmaril.Containers.Fixtures.http_vpre, Silmaril.Containers.Http.okResponse_parses, …
```

## In the explorer

The **Containers** tab (`#/containers`, built by `make pages`) lists the examples with the
registry's verdicts; each example's page shows its image, shape, digests, runtime, machine,
policy, profile, specification, the proved run, the run computed now, the theorems with their
sources, and the registry's shape, arguments and answers.

## What the verdicts rest on

| | |
| --- | --- |
| Real | The bytes (SHA-256 checked in the kernel), read by the restricted OCI reader (`Containers.Oci`), loaded by LPS's x86-64 loader, run by the LPS model of Linux (`Containers.Lps`) for every resolution of x86's undefined flags and every launch LPS admits. `docker-test.sh` runs the same image under Docker as a test. |
| Model | A small program of a model machine (`Mini`, the fixtures' `Tiny`) standing for the container's program. The HTTP response is parsed by the verified HTTP/1.1 parser (`Http.okResponse_parses`); the HTTP interface is valid and admissible under `tcpOnly` (`Http.httpIface_valid`, `httpIface_admissible`). |
| Every example | No undefined behaviour is part of every verified specification; thread creation is undefined under the sequential clone policy; the machine is a parameter of the runtime (`Mach.MachRuntime`). |
