#!/bin/sh
# Use Ubuntu's signed archives over HTTPS rather than the runner's HTTP mirror list.
# Keep suites, components, signing keys and package selections unchanged.
set -eu
for file in /etc/apt/sources.list /etc/apt/sources.list.d/ubuntu.sources; do
  [ -f "$file" ] || continue
  sed -i \
    -e 's|mirror+file:/etc/apt/apt-mirrors.txt|https://archive.ubuntu.com/ubuntu|g' \
    -e 's|mirror+file:/etc/apt/apt-mirrors-security.txt|https://security.ubuntu.com/ubuntu|g' \
    -e 's|http://azure.archive.ubuntu.com/ubuntu|https://archive.ubuntu.com/ubuntu|g' \
    -e 's|http://archive.ubuntu.com/ubuntu|https://archive.ubuntu.com/ubuntu|g' \
    -e 's|http://security.ubuntu.com/ubuntu|https://security.ubuntu.com/ubuntu|g' \
    -e 's|http://ports.ubuntu.com/ubuntu-ports|https://ports.ubuntu.com/ubuntu-ports|g' \
    "$file"
done
