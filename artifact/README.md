# Instructions for getting the VM up and running #

1. Download and install [vagrant][].

2. Download and install the 3110 virtual machine.
        
        git clone https://github.com/cs3110/vagrant-opam.git
        cd vagrant-opam
        vagrant up

   **Note:** `vagrant up` will take a long time (about an hour) the first time.

3. Log into your new virtual machine.

        vagrant ssh

4. When you are done, log out by typing `control-D`.

5. The virtual machine is still running.  You can suspend it by typing

        vagrant suspend

   and then restart it later by typing

        vagrant up

6. You can also control your VM through VirtualBox itself.

[vagrant]: http://www.vagrantup.com/downloads.html
