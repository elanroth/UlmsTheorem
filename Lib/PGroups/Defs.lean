import Lib.PGroups.Heights

/-!
# Reduced abelian p-groups: legacy compatibility import

Historically the core algebra for reduced abelian `p`-groups lived in this file.
It now re-exports the reorganized `PGroups` layer:

- `Lib.PGroups.Subgroups`
- `Lib.PGroups.UlmSubgroups`
- `Lib.PGroups.Heights`

Existing imports of `Lib.PGroups.Defs` therefore continue to work while the
library is migrated to the new layout.
-/
