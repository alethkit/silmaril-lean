FROM debian:trixie-20251103@sha256:01a723bf5bfb21b9dda0c9a33e0538106e4d02cce8f557e118dd61259553d598

# TLS bootstrap for the slim image. APT still verifies Debian's signed archive.
RUN --mount=type=secret,id=bootstrap_ca,required=true,mode=0444 \
    rm /etc/apt/sources.list.d/debian.sources \
    && printf '%s\n' 'deb [check-valid-until=no] https://snapshot.debian.org/archive/debian/20251103T000000Z trixie main' > /etc/apt/sources.list \
    && apt-get -o Acquire::https::CaInfo=/run/secrets/bootstrap_ca -o Acquire::Retries=2 -o Acquire::https::Timeout=25 update \
    && apt-get -o Acquire::https::CaInfo=/run/secrets/bootstrap_ca -o Acquire::Retries=2 -o Acquire::https::Timeout=25 install -y --no-install-recommends \
        gcc=4:14.2.0-1 gcc-14=14.2.0-19 clang-19=1:19.1.7-3+b1 \
        libc6-dev=2.41-12 binutils=2.44-3 \
    && rm -rf /var/lib/apt/lists/*
