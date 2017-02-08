libraries/compact_PACKAGE = compact
libraries/compact_dist-install_GROUP = libraries
$(if $(filter compact,$(PACKAGES_STAGE0)),$(eval $(call build-package,libraries/compact,dist-boot,0)))
$(if $(filter compact,$(PACKAGES_STAGE1)),$(eval $(call build-package,libraries/compact,dist-install,1)))
$(if $(filter compact,$(PACKAGES_STAGE2)),$(eval $(call build-package,libraries/compact,dist-install,2)))
