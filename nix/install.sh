#!/bin/sh

# shell practice, attempting to understand nix installer

# This script installs the Nix package manager on your system by
# downloading a binary distribution and running its installer script
# (which in turn creates and populates /nix).


oops () 
{
    echo "$0:" "$@" >&2
    exit 1
}

dirPat="nix-binary-tarball-unpack.XXXXXXXXXX"
dirErr="Can't create temporary directory for downloading the Nix binary tarball"


# restore this line for real
# tmpDir="$(mktemp -d -t $dirPat || oops $dirErr)"

# avoid new file download
tmpDir="/tmp/nix-binary-tarball-unpack.GNmrwMEdVQ"

cleanup ()
{
    echo "Cleaning up temporary directory $tmpDir"
    rm -rf $tmpDir
}

# don't clean up so we keep the cached dowload
# trap cleanup EXIT INT QUIT TERM


hash1="7ce46548509837d4bc8d01b63973f8fb8972fbbe8ba6a9b5e929cf5954c3d85e"
hash2="b055b9ac5e65d43cb6b1d1fe99eb106371a6b5782c3522209a73f473dc7b8779"
hash3="1d5c5ede3d7be3963f34f6b51a7b37b3ce3adc5ce623f2a50c11501b9c95bd4e"
hash4="2286e52c2047fcc23ac0dec030eb1f69da1be2983b0defd744b1acbe285db1f7"

case "$(uname -s).$(uname -m)" in
    Linux.x86_64)  system=x86_64-linux;  hash=$hash1;;
    Linux.i?86)    system=i686-linux;    hash=$hash2;;
    Linux.aarch64) system=aarch64-linux; hash=$hash3;;
    Darwin.x86_64) system=x86_64-darwin; hash=$hash4;;
    *) oops "sorry, there is no binary distribution of Nix for your platform";;
esac


url="https://nixos.org/releases/nix/nix-2.2.2/nix-2.2.2-$system.tar.bz2"
tarball="$tmpDir/$(basename "$tmpDir/nix-2.2.2-$system.tar.bz2")"

installed ()
{
    type "$1" > /dev/null 2>&1
}

require_util() 
{
    installed "$1" || oops "you do not have '$1' installed, which I need to $2"
}

require_util curl  "download the binary tarball"
require_util bzcat "decompress the binary tarball"
require_util tar   "unpack the binary tarball"

echo "downloading Nix 2.2.2 binary tarball for $system"
echo "from: '$url'"
echo "to: '$tmpDir'"

# don't actually download file, we have it cached
# curl -L $url -o $tarball || oops "failed to download '$url'"

# We decided to use 'curl' but 'wget' could have been used too
# wget $url -P $tmpDir || oops "failed to download '$url'"

check_hash ()
{
    echo "checking hash of downloaded tarball"
    if installed sha256sum; then
        check="$(sha256sum -b ${tarball} | cut -c1-64)"
    elif installed shasum; then
        check="$(shasum -a 256 -b ${tarball} | cut -c1-64)"
    elif installed openssl; then
        check="$(openssl dgst -r -sha256 ${tarball} | cut -c1-64)"
    else
        oops "Expecting one of 'sha256sum', 'shasum' or 'openssl' to be installed"
    fi

    if [ "$hash" != "$check" ]; then
        oops "SHA-256 hash mismatch in ${url}: got ${check}, expecting ${hash}"
    else
        echo "hash was successfully checked"
    fi
}

check_hash

unpack="${tmpDir}/unpack"

# already cached
# mkdir -p "${unpack}"
# < "$tarball" bzcat | tar -xf - -C "$unpack" || oops "failed to unpack '$url'"

echo "finding additional script file"
script=$(echo "$unpack"/*/install)
echo ${script}

if [ -e "$script" ]; then
    echo "additional script file does exist"
else
    oops "additional script file is missing"
fi

