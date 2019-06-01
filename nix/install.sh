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
tmpDir="/tmp/nix-binary-tarball-unpack.46oIt0Ly37"

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

set -e
dest="/nix"
self="/tmp/nix-binary-tarball-unpack.46oIt0Ly37/unpack/nix-2.2.2-x86_64-linux"
nix="/nix/store/hbhdjn5ik3byg642d1m11k3k3s0kn3py-nix-2.2.2"
cacert="/nix/store/rikxx4wdaj7b4qp1lizzmn7884hh537k-nss-cacert-3.42"

if ! [ -e "$self/.reginfo" ]; then
    echo "$0: incomplete installer (.reginfo is missing)"
    exit 1
fi

if [ -z "$USER" ]; then
    echo "$0: \$USER is not set"
    exit 1
fi


if [ -z "$HOME" ]; then
    echo "$0: \$HOME is not set"
    exit 1
fi

if [ "$(uname -s)" = "Linux" ] && [ -e /run/systemd/system ]; then
    echo "Note: a multi-user installation is possible."
    echo "See https://nixos.org/nix/manual/#sect-multi-user-installation"
fi

echo "performing a single-user installation of Nix..."


mkdir -p $dest/store

printf "copying Nix to %s..." "${dest}/store"
for i in $(cd "$self/store" >/dev/null && echo ./*); do
    printf "." >&2
    i_tmp="$dest/store/$i.$$"
    if [ -e "$i_tmp" ]; then
        rm -rf "$i_tmp"
    fi
    if ! [ -e "$dest/store/$i" ]; then
        cp -Rp "$self/store/$i" "$i_tmp"
        chmod -R a-w "$i_tmp"
        chmod +w "$i_tmp"
        mv "$i_tmp" "$dest/store/$i"
        chmod -w "$dest/store/$i"
    fi
done
echo ""

echo "initialising Nix database..."
if ! $nix/bin/nix-store --init; then
    echo "$0: failed to initialize the Nix database"
    exit 1
fi

if ! "$nix/bin/nix-store" --load-db < "$self/.reginfo"; then
    echo "$0: unable to register valid paths"
    exit 1
fi

. "$nix/etc/profile.d/nix.sh"

if ! "$nix/bin/nix-env" -i "$nix"; then
    echo "$0: unable to install Nix into your default profile"
    exit 1
fi



