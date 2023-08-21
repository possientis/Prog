#!/bin/sh

DIR=$(pwd)

cd ${HOME}/Prog/dot

sudo usermod -aG kvm ${USER} 
sudo usermod -aG libvirt ${USER}
sudo usermod -aG libvirt-qemu ${USER}

cd ${HOME}
mkdir -p VMs
sudo chown root:kvm VMs
sudo chmod g+rw VMs

cd VMs
sudo mkdir -p images
sudo chown root:kvm images
sudo chmod g+rw images

cd images
sudo mkdir -p ISO
sudo chown libvirt-qemu:libvirt-qemu ISO

echo "You need to add symlinks in ~/VMs/images/ISO owned by ${USER}:kvm"

cd /var/lib/libvirt
sudo rm images -rf
sudo ln -nfs ${HOME}/VMs/images images

echo "You need to edit the file /etc/libvirt/qemu.conf, and set:"
echo "user = \"${USER}\""
echo "group = \"libvirt\""
echo "after you have done that:"
echo "$ sudo systemctl restart libvirtd"








cd $DIR
