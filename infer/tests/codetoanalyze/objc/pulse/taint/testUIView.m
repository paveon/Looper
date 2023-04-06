/*
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#import <UIKit/UIKit.h>
#import "CoreGraphics/CoreGraphics.h"

@interface TestUIView : UIView
@property int number;
- (id)initWithNumber:(int)n;
- (int)getNumber;
- (void)setNumber:(int)n;
@end

@implementation TestUIView

- (id)initWithNumber:(int)n {
  self = [super initWithFrame:CGRectZero];
  if (self) {
    self.number = n;
  }
  return self;
}

- (void)setNumber:(int)n {
  self.number = n;
}

- (int)getNumber {
  return self.number;
}
@end

TestUIView* TestUIViewCreate(int number) {
  return [[TestUIView alloc] initWithNumber:number];
}

void testUIView_initWithFrameNPEBad() {
  TestUIView* view = TestUIViewCreate(0);
  if (view) {
    int* p = NULL;
    *p = 0;
  }
}
