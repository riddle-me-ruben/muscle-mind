from flask import session, request, redirect, url_for, render_template

class QuizSubmissionManager:
    def __init__(self, db_manager, retrieval_manager):
        self.db_manager = db_manager
        self.retrieval_manager = retrieval_manager

    def take_quiz(self, quiz_id, question_num):
        quiz = self.retrieval_manager.get_quiz_by_id(quiz_id)
        if question_num >= len(quiz['questions']):
            return redirect(url_for('home'))
        return render_template('take-quiz.html', quiz=quiz, question_num=question_num, quiz_id=quiz_id)

    def submit_quiz_answer(self, quiz_id, question_num):
        quiz = self.retrieval_manager.get_quiz_by_id(quiz_id)
        user_answer = request.form.get('answer')
        correct_answer = quiz['questions'][question_num]['correct_option']
        current_score = session.get('current_score', 0)

        if user_answer == correct_answer:
            session['current_score'] = current_score + 1
            if question_num + 1 < len(quiz['questions']):
                return redirect(url_for('take_quiz_route', quiz_id=quiz_id, question_num=question_num + 1))
            else:
                return redirect(url_for('score_route', quiz_id=quiz_id, score=session['current_score'], total=len(quiz['questions'])))
        else:
            return redirect(url_for('penalty_route', quiz_id=quiz_id, question_num=question_num))

    def score(self, quiz_id, score, total):
        session.pop('current_score', None)
        return render_template('score.html', score=score, total=total)

    def penalty(self, quiz_id, question_num):
        quiz = self.retrieval_manager.get_quiz_by_id(quiz_id)
        return render_template('penalty.html', quiz_id=quiz_id, question_num=question_num, total_questions=len(quiz['questions']), score=session.get('current_score', 0))
