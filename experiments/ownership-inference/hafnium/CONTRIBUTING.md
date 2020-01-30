# How to Contribute

We'd love to accept your patches and contributions to this project. There are
just a few small guidelines you need to follow.

## Contributor License Agreement

Contributions to this project must be accompanied by a Contributor License
Agreement. You (or your employer) retain the copyright to your contribution;
this simply gives us permission to use and redistribute your contributions as
part of the project. Head over to <https://cla.developers.google.com/> to see
your current agreements on file or to sign a new one.

You generally only need to submit a CLA once, so if you've already submitted one
(even if it was for a different project), you probably don't need to do it
again.

## Style guide

Submissions should follow the Hafnium [style guide](docs/StyleGuide.md).

## Code reviews

All submissions, including submissions by project members, require review. We
use [Gerrit](https://hafnium-review.googlesource.com) for this purpose.

To submit a change:

1.  Create an account in the
    [Gerrit UI](https://hafnium-review.googlesource.com).
2.  Follow the [getting started](docs/GettingStarted.md) instructions to clone
    the Hafnium repositories and set up the necessary commit hook.
3.  Make your change.
4.  Run our autoformatter with `make format`.
5.  Commit as usual. If you make a change in a submodule you will also need to
    commit a change in the main repository to update the submodule version.
6.  Run the [tests](docs/Testing.md) and other presubmit checks with
    `kokoro/build.sh`, ensure they all pass.
7.  Upload the change to Gerrit with `git push origin HEAD:refs/for/master`. If
    you have changed submodules then you'll need to push them as well.
8.  If you changed submodules, then add a matching 'topic' from the Gerrit UI
    for all your changes (submodules and the main repository) so that they can
    be reviewed and submitted together.
9.  Wait 10-15 minutes for our presubmit tests to run, and make sure a 'Kokoro
    +1' comment shows up in Gerrit indicating that they have passed. If not,
    follow the links to find the errors, fix them and try again.
10. From the Gerrit UI add one or more reviewers. Looking at who has modified
    the same files frequently recently is usually a good way to pick a reviewer,
    but if you're not sure then you can add hafnium-team@google.com.

## Community Guidelines

This project follows
[Google's Open Source Community Guidelines](https://opensource.google.com/conduct/).
