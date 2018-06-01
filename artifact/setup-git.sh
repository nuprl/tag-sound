cat > ~/.gitconfig <<EOF

[credential]
	helper = store

[alias]
	co = checkout
	ci = commit
	stat = status

[push]
	default = simple

EOF

echo "alias gits=git status" >> $HOME/.zshrc
