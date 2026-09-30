#!/usr/bin/env bash
set -euo pipefail

artifact_dir=$(cd "$(dirname "$0")" && pwd)
cd "$artifact_dir/.."

image=eq-checking-abstract-interpretation-lean
docker build -t "$image" .
docker save -o "$artifact_dir/$image-image.tar" "$image"

cd "$artifact_dir"
rm -f "$image.zip"
zip -q -0 -r "$image.zip" . -x './prepare-artifact.sh' "./$image.zip" "./$image-image.tar.gz"