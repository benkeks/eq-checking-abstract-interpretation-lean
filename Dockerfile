FROM ubuntu:24.04

ARG LEAN_VERSION=4.34.1
RUN apt-get update \
    && DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends ca-certificates curl git time zstd \
    && rm -rf /var/lib/apt/lists/*

RUN curl -fsSL "https://github.com/leanprover/lean4/releases/download/v${LEAN_VERSION}/lean-${LEAN_VERSION}-linux.tar.zst" \
    | tar --use-compress-program=unzstd -x -C /opt
ENV PATH="/opt/lean-${LEAN_VERSION}-linux/bin:${PATH}"

WORKDIR /artifact
COPY . .

RUN lake update \
    && lake exe cache get \
    && lake build

ENTRYPOINT []
CMD ["bash"]