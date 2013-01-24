#ifndef _URCU_ARCH_UATOMIC_TILE_H
#define _URCU_ARCH_UATOMIC_TILE_H

/*
 * Copyright (c) 2013 Simon Marchi <simon.marchi@polymtl.ca>
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA
 */

#ifdef __tilegx__
#include <urcu/uatomic/gcc.h>
#else
#error "URCU has only been tested on the TileGx architecture. For other Tile* architectures, please run the tests first and report the results to the maintainer so that proper support can be added."
#endif

#endif /* _URCU_ARCH_UATOMIC_TILE_H */
