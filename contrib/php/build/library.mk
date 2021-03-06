#  +----------------------------------------------------------------------+
#  | PHP Version 4                                                        |
#  +----------------------------------------------------------------------+
#  | Copyright (c) 1997-2002 The PHP Group                                |
#  +----------------------------------------------------------------------+
#  | This source file is subject to version 2.02 of the PHP license,      |
#  | that is bundled with this package in the file LICENSE, and is        |
#  | available at through the world-wide-web at                           |
#  | http://www.php.net/license/2_02.txt.                                 |
#  | If you did not receive a copy of the PHP license and are unable to   |
#  | obtain it through the world-wide-web, please send a note to          |
#  | license@php.net so we can mail you a copy immediately.               |
#  +----------------------------------------------------------------------+
#  | Author: Sascha Schumann <sascha@schumann.cx>                         |
#  +----------------------------------------------------------------------+
#
# $Id: library.mk,v 1.12 2002/02/28 08:25:33 sebastian Exp $ 
#

LTLIBRARY_OBJECTS = $(LTLIBRARY_SOURCES:.c=.lo) $(LTLIBRARY_OBJECTS_X)

$(LTLIBRARY_NAME): $(LTLIBRARY_OBJECTS) $(LTLIBRARY_DEPENDENCIES)
	$(LINK) $(LTLIBRARY_LDFLAGS) $(LTLIBRARY_OBJECTS) $(LTLIBRARY_LIBADD)
