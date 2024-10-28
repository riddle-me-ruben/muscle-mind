import unittest
from unittest.mock import MagicMock, patch
from src.server.QuizManager import QuizManager
from src.server.QuizCreationManager import QuizCreationManager
from src.server.QuizRetrievalManager import QuizRetrievalManager
from src.server.QuizSubmissionManager import QuizSubmissionManager


class TestQuizManager(unittest.TestCase):
    def setUp(self):
        self.mock_db_manager = MagicMock()
        self.mock_session = {'email': 'test_user@example.com'}
        self.quiz_manager = QuizManager(self.mock_db_manager, self.mock_session)
        
    @patch.object(QuizCreationManager, 'create_quiz')
    def test_create_quiz(self, mock_create_quiz):
        mock_create_quiz.return_value = "Quiz Creation Form"
        response = self.quiz_manager.create_quiz()
        mock_create_quiz.assert_called_once()
        self.assertEqual(response, "Quiz Creation Form")

    @patch.object(QuizCreationManager, 'submit_quiz')
    def test_submit_quiz(self, mock_submit_quiz):
        mock_submit_quiz.return_value = "Quiz Submitted Successfully"
        response = self.quiz_manager.submit_quiz()
        mock_submit_quiz.assert_called_once()
        self.assertEqual(response, "Quiz Submitted Successfully")

    @patch.object(QuizRetrievalManager, 'get_user_quizzes')
    def test_get_user_quizzes(self, mock_get_user_quizzes):
        mock_quizzes = [{'id': 1, 'title': 'Sample Quiz'}]
        mock_get_user_quizzes.return_value = mock_quizzes
        response = self.quiz_manager.get_user_quizzes('test_user@example.com')
        mock_get_user_quizzes.assert_called_once_with('test_user@example.com')
        self.assertEqual(response, mock_quizzes)

    @patch.object(QuizRetrievalManager, 'quiz_detail')
    def test_quiz_detail(self, mock_quiz_detail):
        mock_quiz_detail.return_value = "Quiz Detail Page"
        response = self.quiz_manager.quiz_detail(1)
        mock_quiz_detail.assert_called_once_with(1)
        self.assertEqual(response, "Quiz Detail Page")

    @patch.object(QuizSubmissionManager, 'take_quiz')
    def test_take_quiz(self, mock_take_quiz):
        mock_take_quiz.return_value = "Quiz Question Page"
        response = self.quiz_manager.take_quiz(quiz_id=1, question_num=1)
        mock_take_quiz.assert_called_once_with(1, 1)
        self.assertEqual(response, "Quiz Question Page")

    @patch.object(QuizSubmissionManager, 'submit_quiz_answer')
    def test_submit_quiz_answer(self, mock_submit_quiz_answer):
        mock_submit_quiz_answer.return_value = "Next Question or Score Page"
        response = self.quiz_manager.submit_quiz_answer(quiz_id=1, question_num=1)
        mock_submit_quiz_answer.assert_called_once_with(1, 1)
        self.assertEqual(response, "Next Question or Score Page")

    @patch.object(QuizSubmissionManager, 'score')
    def test_score(self, mock_score):
        mock_score.return_value = "Score Page Displayed"
        response = self.quiz_manager.score(quiz_id=1, score=8, total=10)
        mock_score.assert_called_once_with(1, 8, 10)
        self.assertEqual(response, "Score Page Displayed")

    @patch.object(QuizSubmissionManager, 'penalty')
    def test_penalty(self, mock_penalty):
        mock_penalty.return_value = "Penalty Page Displayed"
        response = self.quiz_manager.penalty(quiz_id=1, question_num=2)
        mock_penalty.assert_called_once_with(1, 2)
        self.assertEqual(response, "Penalty Page Displayed")

if __name__ == '__main__':
    unittest.main()
